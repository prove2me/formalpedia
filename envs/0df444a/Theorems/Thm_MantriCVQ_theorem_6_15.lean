-- Prove2me | Theorems.Thm_MantriCVQ_theorem_6_15
-- name    : MantriCVQ.theorem_6_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:12:21.76142+00:00
-- url     : https://prove2.me/theorems/4e8514f1-bd01-4c3c-b981-c1ead6c8adc9
-- title:
--   Theorem 6.15 — switching with pointwise error, Eq. (6.4)
-- statement:
--   Fix a level $u\ge0$ and an exponent $\alpha\ge0$, and put $j=\lfloor\alpha\rfloor+1$, $\nu=m_{u+j-1}$. Consider an instance of size $n$ and height $h$ with $u+j\le h\le h_{\max}(n)$, and let $\rho=\rho_u\circ\cdots\circ\rho_{u+j-1}$. For all sufficiently large $n$, for every $W$ with $1\le W\le n^\alpha$, every CNF $\Psi$ of width at most $W$ on the node values at level $u-1$ and every integer $q\ge1$, there is a random DNF $\widetilde\Psi_\rho$ on the node values at level $u+j-1$, determined by $\Psi$, $q$ and $\rho$, with at most $2^{Wq}$ terms of width at most $Wq$. For every $z$ it satisfies $\widetilde\Psi_\rho(z)\le\Psi(\rho(z))$, and for every fixed $z$
--   $$\Pr_\rho\bigl[\widetilde\Psi_\rho(z)\ne\Psi(\rho(z))\bigr]\le2\cdot2^{-\nu(q+1)/(30W)}.$$
--   The dual statement switches a DNF of width at most $W$ to a CNF that is at least the projected DNF everywhere, with the same bounds. The threshold on $n$ depends only on $u$, $\alpha$ and $d$, and not on $h$. Both statements are part of this item.
--
--   Differences from the source:
--   - generalization: a code family of Definition 3.1 → any family with the degree condition (CodeDeg d); reason: the paper says the switching argument uses the code family only through the degree bound (p. 6); every code family of Definition 3.1 qualifies
--   - reading: for all sufficiently large n, with thresholds depending only on u, alpha and d → one n0 chosen before the family, for given d, u and alpha; reason: this is what the paper's sentence on the thresholds says
--   - encoding: node values at level u + j - 1 and at level u - 1 → addresses of the level-(u+j-1) nodes, and pairs of such an address and an address inside its block; reason: a level-(u-1) node lies in exactly one block
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Theorem 6.15, Eq. (6.4), p. 33 (PDF p. 35)

import Mathlib
import Definitions.Def_MantriCVQ_CNF
import Definitions.Def_MantriCVQ_CodeDeg
import Definitions.Def_MantriCVQ_Forest
import Definitions.Def_MantriCVQ_Pr
import Definitions.Def_MantriCVQ_dimsRange
import Definitions.Def_MantriCVQ_listWidth

open QAlgorithms.Complexity SamplingAC0

namespace MantriCVQ

/-- **Theorem 6.15** (Mantri, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Theorem 6.15, Eq. (6.4), p. 33 (PDF p. 35)): fix `u` and `α ≥ 0`, and put
`j = ⌊α⌋ + 1`, `ν = m_{u+j-1}`. For an instance of size `n` and height `h` with `u + j ≤ h ≤ h_max(n)` and `n`
sufficiently large, for every `1 ≤ W ≤ n^α`, every CNF `Ψ` of width at most `W` on the node values at level
`u - 1` and every `q ≥ 1` there is a random DNF `Ψ̃_ρ` on the node values at level `u + j - 1` with at most
`2^{Wq}` terms of width at most `Wq`, determined by `Ψ`, `q`, `ρ`, with `Ψ̃_ρ(z) ≤ Ψ(ρ(z))` for every `z` and
`Pr_ρ[Ψ̃_ρ(z) ≠ Ψ(ρ(z))] ≤ 2 · 2^{-ν(q+1)/(30W)}` for every fixed `z`. The dual statement switches a DNF of
width at most `W` to a CNF at least the projected DNF everywhere, with the same bounds.

**Formalization Note** A node at level `u + j - 1` is named by its address `ι` from the root, and a node at
level `u - 1` by a block and an address inside it. The random DNF is a function of the seeds, so it does not
see `z`. `n₀` is chosen before the code family and `h`: it depends only on `u`, `α`, `d`. -/
theorem theorem_6_15 (d u : ℕ) (α : ℝ) (hα : 0 ≤ α) :
    ∃ n₀ : ℕ, ∀ (C : CodeDeg d) (n h : ℕ), n₀ ≤ n → u + (⌊α⌋₊ + 1) ≤ h → h ≤ hmax n →
      ∀ W : ℕ, 1 ≤ W → (W : ℝ) ≤ (n : ℝ) ^ α → ∀ q : ℕ, 1 ≤ q →
      (∀ Ψ : CNF (Addr (dimsRange n (u + (⌊α⌋₊ + 1)) (h - (u + (⌊α⌋₊ + 1)))) ×
            Addr (dimsRange n u (⌊α⌋₊ + 1))), listWidth Ψ ≤ W →
        ∃ Ψt : (Addr (dimsRange n (u + (⌊α⌋₊ + 1)) (h - (u + (⌊α⌋₊ + 1)))) →
              Seed (dimsRange n u (⌊α⌋₊ + 1))) →
            DNF (Addr (dimsRange n (u + (⌊α⌋₊ + 1)) (h - (u + (⌊α⌋₊ + 1))))),
          (∀ s, (Ψt s).length ≤ 2 ^ (W * q) ∧ listWidth (Ψt s) ≤ W * q ∧
            ∀ z, DNF.eval (Ψt s) z = true →
              CNF.eval Ψ (forestInput C.code (dimsRange n u (⌊α⌋₊ + 1)) s z) = true) ∧
          ∀ z, Pr (fun s => DNF.eval (Ψt s) z ≠
              CNF.eval Ψ (forestInput C.code (dimsRange n u (⌊α⌋₊ + 1)) s z)) ≤
            2 * (2 : ℝ) ^ (-((dim n (u + (⌊α⌋₊ + 1) - 1) : ℝ) * (q + 1) / (30 * W)))) ∧
      (∀ Φ : DNF (Addr (dimsRange n (u + (⌊α⌋₊ + 1)) (h - (u + (⌊α⌋₊ + 1)))) ×
            Addr (dimsRange n u (⌊α⌋₊ + 1))), listWidth Φ ≤ W →
        ∃ Φt : (Addr (dimsRange n (u + (⌊α⌋₊ + 1)) (h - (u + (⌊α⌋₊ + 1)))) →
              Seed (dimsRange n u (⌊α⌋₊ + 1))) →
            CNF (Addr (dimsRange n (u + (⌊α⌋₊ + 1)) (h - (u + (⌊α⌋₊ + 1))))),
          (∀ s, (Φt s).length ≤ 2 ^ (W * q) ∧ listWidth (Φt s) ≤ W * q ∧
            ∀ z, DNF.eval Φ (forestInput C.code (dimsRange n u (⌊α⌋₊ + 1)) s z) = true →
              CNF.eval (Φt s) z = true) ∧
          ∀ z, Pr (fun s => CNF.eval (Φt s) z ≠
              DNF.eval Φ (forestInput C.code (dimsRange n u (⌊α⌋₊ + 1)) s z)) ≤
            2 * (2 : ℝ) ^ (-((dim n (u + (⌊α⌋₊ + 1) - 1) : ℝ) * (q + 1) / (30 * W)))) := by sorry

end MantriCVQ
