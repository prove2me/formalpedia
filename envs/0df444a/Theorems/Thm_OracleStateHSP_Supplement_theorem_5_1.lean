-- Prove2me | Theorems.Thm_OracleStateHSP_Supplement_theorem_5_1
-- name    : OracleStateHSP.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:14:41.641163+00:00
-- url     : https://prove2.me/theorems/af21defd-e737-4f37-bc1a-bbe1871c1381
-- title:
--   Theorem 5.1 — sample lower bound: $\Omega(\log|G/H|/\varepsilon)$ copies, even with collective measurements
-- statement:
--   Let $\varepsilon \in (0, 1]$ and $r, m \in \mathbb N$ with $m \ge 1$, and let $G = \mathbb Z_2^r \oplus \mathbb Z_2^{2m}$ (so $G = \mathbb Z_2^{r+2m}$). Let $R$ be the left-regular shift $R(g)|x\rangle|a\rangle = |x+g\rangle|a\rangle$ on $\mathbb C^{|G|} \otimes \mathbb C^2$ (eq. (69)). The hard family consists of the state vectors
--   $$
--   |\varphi^\varepsilon_{H,\alpha}\rangle = \sqrt{1-\varepsilon}\, |u_G\rangle|0\rangle + e^{i\alpha}\sqrt{\varepsilon}\, |H\rangle|1\rangle \qquad \text{(eq. (70))}
--   $$
--   for every subgroup $H = \mathbb Z_2^r \oplus \tilde H$ with $\tilde H$ an $m$-dimensional subspace of $\mathbb Z_2^{2m}$ (eq. (72)) and every phase $\alpha \in [0, 2\pi)$.
--
--   **Theorem.** There is a universal constant $c > 0$ such that for all such $\varepsilon, r, m$:
--
--   1. every member of the family is a StateHSP instance (Definition 1.2) with hidden subgroup $H$ and parameter $\varepsilon$, and $|G/H| = 2^m$, i.e. $\log_2|G/H| = m$ is known;
--   2. every $t$-sample algorithm, i.e. every fixed POVM, independent of the instance, acting collectively on $|\varphi^\varepsilon_{H,\alpha}\rangle^{\otimes t} \otimes |0\rangle_W$ with a workspace $W$ of any finite dimension, whose outcome is reported as a subgroup, that identifies the hidden subgroup with probability at least $2/3$ on every member of the family uses
--   $$
--   t \;\ge\; c \cdot \frac{m}{\varepsilon} \;=\; c \cdot \frac{\log_2 |G/H|}{\varepsilon}
--   $$
--   copies.
--
--   Together with the copy-based sampler (Theorem 3.8) and Algorithm 1, this shows that $\Theta\big(\log|G/H|/\varepsilon\big)$ copies are necessary and sufficient for abelian StateHSP at constant error, and that the dependence on $|G/H|$ rather than $|G|$ is optimal.
--
--   **Formalization Note** The constant $c$ is chosen before $\varepsilon$, $r$ and $m$. The POVM is the published `FuchsVdGraaf.IsPOVM` (positive semidefinite effects summing to the identity) with outcomes $\{0, \dots, e-1\}$ and an output map to subgroups of $G$; the workspace has dimension $b + 1$ for arbitrary $b$.
--
--   Differences from the source:
--   - reading: Ω(log(|G/H|)/ε) copies → one constant c > 0, chosen before ε, r and m, with c·m/ε ≤ t; reason: the proof gives m²/6 ≤ I(H;Z) ≤ 2tεm, i.e. t ≥ m/(12ε), for every ε, r and m ≥ 1, so the uniform reading of Ω holds
--   - generalization: there is a family of abelian StateHSP instances → the explicit family of eqs. (69)–(72), with its instance validity and |G/H| = 2^m as conjuncts; reason: the paper's own family witnesses the existential
--   - encoding: G = Z_2^{r+2m} = Z_2^r ⊕ Z_2^{2m} → K r × V (2m), i.e. (Fin r → ZMod 2) × (Fin (2m) → ZMod 2); reason: the direct-sum decomposition the paper uses
--   - encoding: m-dimensional subspaces H̃ of Z_2^{2m} → additive subgroups of V (2m) with 2^m elements; reason: over Z_2 every additive subgroup is a subspace, and dimension m means 2^m elements
--   - generalization: a workspace W of qubits initialized to |0⟩ → a workspace of dimension b + 1 for every b, initialized to its first basis vector; reason: includes every qubit workspace (b + 1 = 2^q), so the lower bound covers more algorithms
--   - encoding: a POVM whose measurement returns s(x) → a POVM with outcomes Fin e (FuchsVdGraaf.IsPOVM) and an output map to subgroups; reason: coarse-graining a POVM by the output map is a POVM with outcomes in the answer set
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, Theorem 5.1, p.41; eqs. (69)–(72), pp.43–44; Definition 5.2, p.41

import Mathlib
import Definitions.Def_FuchsVdGraaf_IsPOVM
import Definitions.Def_OracleStateHSP_Supplement_IsStateHSPSampleInstance
import Definitions.Def_OracleStateHSP_Supplement_regShift
import Definitions.Def_OracleStateHSP_Supplement_phiS
import Definitions.Def_OracleStateHSP_Supplement_padSub
import Definitions.Def_OracleStateHSP_Supplement_copiesState
import Definitions.Def_OracleStateHSP_Supplement_successProb
set_option synthInstance.maxSize 1024

namespace OracleStateHSP

namespace Supplement

/-- **Theorem 5.1 (Sample lower bound)** (Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, Theorem 5.1, p.41; family eqs. (69)–(72),
pp.43–44; model Definition 5.2, p.41). There is one universal `c > 0` such that for every
`ε ∈ (0, 1]` and all `r, m ∈ ℕ` with `m ≥ 1`, on `G = Z_2^r ⊕ Z_2^(2m)` (so `G = Z_2^(r+2m)`) the
family `|φ^ε_(H,α)⟩` (eq. (70)), with `R` the left-regular shift (eq. (69)), `H = Z_2^r ⊕ H̃` for
every `m`-dimensional subspace `H̃ ≤ Z_2^(2m)` (eq. (72)) and every phase `α ∈ [0, 2π)`, satisfies:

1. every member is a StateHSP instance (Definition 1.2) with hidden subgroup `H` and parameter
   `ε`, and `|G/H| = 2^m` (so `log₂|G/H| = m`);
2. every `t`-sample algorithm (a fixed POVM `{M_z}`, independent of the instance, acting
   collectively on `|φ⟩^(⊗t) ⊗ |0⟩_W` with a workspace `W` of any finite dimension, followed by an
   output map `out`) that returns `H` with probability at least `2/3` on every member uses
   `t ≥ c · m / ε` copies.

**Formalization Note.** `Ω` is one constant chosen before `ε`, `r` and `m`. `Z_2^r` and
`Z_2^(2m)` are the published `K r` and `V (2m)`; the `m`-dimensional subspaces of `Z_2^(2m)` are the
additive subgroups with `2^m` elements. The POVM is `FuchsVdGraaf.IsPOVM` (positive semidefinite
effects summing to the identity) with outcomes `Fin e`; `W` has basis `Fin (b + 1)`. -/
theorem theorem_5_1 :
    ∃ c : ℝ, 0 < c ∧
    ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
    ∀ (r m : ℕ), 1 ≤ m →
      (∀ Ht : AddSubgroup (V (2 * m)), Nat.card Ht = 2 ^ m →
        ∀ α : ℝ, 0 ≤ α → α < 2 * Real.pi →
          IsStateHSPSampleInstance regShift (phiS ε (padSub r m Ht) α) (padSub r m Ht) ε ∧
          Nat.card ((K r × V (2 * m)) ⧸ padSub r m Ht) = 2 ^ m) ∧
      ∀ (t b e : ℕ)
        (Mz : Fin e → Matrix ((Fin t → (K r × V (2 * m)) × Fin 2) × Fin (b + 1))
          ((Fin t → (K r × V (2 * m)) × Fin 2) × Fin (b + 1)) ℂ)
        (out : Fin e → AddSubgroup (K r × V (2 * m))),
        FuchsVdGraaf.IsPOVM Mz →
        (∀ Ht : AddSubgroup (V (2 * m)), Nat.card Ht = 2 ^ m →
          ∀ α : ℝ, 0 ≤ α → α < 2 * Real.pi →
            (2 : ℝ) / 3 ≤ successProb Mz out (copiesState t b (phiS ε (padSub r m Ht) α))
              (padSub r m Ht)) →
        c * (m : ℝ) / ε ≤ t := by sorry

end Supplement

end OracleStateHSP
