-- Prove2me | Theorems.Thm_LoPopescuCC_Dilution_tensorPow_eq_singlets_residual_add_small
-- name    : LoPopescuCC.Dilution.tensorPow_eq_singlets_residual_add_small
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:42:47.375368+00:00
-- url     : https://prove2.me/theorems/adb6cb27-9f0d-4b69-936c-e64ff1c897a2
-- title:
--   Theorem, Eq. (9) — $\psi^N=\Phi^d\otimes\Delta+u_2$ with $d=NS-O(\sqrt N)$, $\Delta$ of Schmidt rank $2^{O(\sqrt N)}$ and $\|u_2\|<\varepsilon$
-- statement:
--   Let $\psi$ be a normalized vector of a finite-dimensional bipartite system and let $S$ be the von Neumann entropy, in bits, of a subsystem of $\psi$. For every $\varepsilon>0$ there are a constant $C$ and $N_0$ such that for every $N\ge N_0$ there are $d,L\in\mathbb N$, isometries $V_A$, $V_B$ from $\mathbb C^{2^d}\otimes\mathbb C^L$ into $\mathcal H_A^{\otimes N}$ and $\mathcal H_B^{\otimes N}$, and an un-normalized vector $\Delta\in\mathbb C^L\otimes\mathbb C^L$ with
--
--   1. $|d-NS|\le C\sqrt N$;
--   2. the Schmidt decomposition of $\Delta$ has at most $2^{C\sqrt N}$ terms;
--   3. $\psi^{N}=(V_A\otimes V_B)(\Phi^{d}\otimes\Delta)+u_2$ with $\|u_2\|<\varepsilon$;
--   4. there is a normalized vector $w$ whose Schmidt coefficients are $2^d$-fold degenerate and whose fidelity with $\psi^N$ satisfies
--   $$
--   |\langle w|\psi^{N}\rangle|^2>1-\varepsilon.
--   $$
--
--   Here $\psi^N$ is the tensor power across the cut $A^N:B^N$ and $\Phi^d$ is $d$ singlets. The constant $C$ depends on $\psi$ and $\varepsilon$ but not on $N$.
--
--   This is what the paper calls the crux of the Letter: up to a small error, $N$ copies of $\psi$ consist of about $NS$ singlets together with a residual state of only $2^{O(\sqrt N)}$ Schmidt terms, which is the structure behind entanglement dilution with $O(\sqrt N)$ bits of classical communication.
--
--   **Formalization Note** $S$ is the published `WildeQIT.EntManip.entEntropy`, the entropy of $\rho^A$. Without the lower bound on $d$ and the bound on the Schmidt rank of $\Delta$ the statement would be trivial ($d=0$, $\Delta=\psi^N$).
--
--   Differences from the source:
--   - reading: d = [NS − O(√N)], Δ has 2^O(√N) terms → d : ℕ with |d − NS| ≤ C√N and SchmidtRank Δ ≤ 2^(C√N), for one C chosen after ψ and ε and before N₀; reason: p. 5 says the coefficient depends on ε; the two-sided bound is the stronger reading of the O(·)
--   - reading: Eq. (9) equates ψ^N with Φ^d ⊗ Δ + u₂, under the convention of Eq. (8) (up to bi-local unitary transformations) → ψ^N = (V_A ⊗ V_B)(Φ^d ⊗ Δ) + u₂ with local isometries V_A, V_B; reason: local dimensions need not be powers of 2, so 2^d L need not equal the dimension of H_A^N; for square matrices the isometries are unitaries
--   - reading: any pure bi-partite state ψ, with the discussion done for pairs of spin 1/2 particles and higher spins called immediate (p. 6) → arbitrary finite local index types a, b; reason: this is the full strength of 'any'; the two-qubit case is the instance a = b = Bool
--   - reading: a state that has D = 2^d degeneracies in its Schmidt decomposition → a unit vector w with IsSchmidtDegenerate (2^d) w, i.e. multiplicities divisible by 2^d; reason: the proof (p. 5) says 'The degeneracies of its Schmidt coefficients are multiples of'
--   - reading: two formulations joined by 'In other words', with fidelity arbitrarily close to 1 and ‖u₂‖ < ε → both are conjuncts for the same d and ε, with fidelity above 1 − ε; reason: keeping both is the full strength of the Theorem
--   - encoding: the von Neumann entropy of a subsystem of ψ → WildeQIT.EntManip.entEntropy, the entropy in bits of ρ^A; reason: the two reduced states of a pure state have the same entropy, and D = 2^d fixes base 2
--   - encoding: fidelity [11] → the squared overlap ‖⟨w, ψ^N⟩‖²; reason: Jozsa's fidelity of two pure states
-- source:
--   Lo, Popescu, The classical communication cost of entanglement manipulation, arXiv:quant-ph/9902045v2, Theorem, p. 4 (continued on p. 5), Eq. (9)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_WildeQIT_EntManip_entEntropy
import Definitions.Def_LoPopescuCC_Dilution_tensorPowCut
import Definitions.Def_LoPopescuCC_Dilution_singletPow
import Definitions.Def_LoPopescuCC_Dilution_schmidtRank
import Definitions.Def_LoPopescuCC_Dilution_IsSchmidtDegenerate
import Definitions.Def_LoPopescuCC_Dilution_pairTensor
import Definitions.Def_LoPopescuCC_Dilution_bilocal

open scoped Matrix

namespace LoPopescuCC.Dilution

/-- **The Theorem** (Lo, Popescu, arXiv:quant-ph/9902045v2, Theorem, pp. 4–5, Eq. (9)). For a pure
bipartite `ψ` with subsystem entropy `S` in bits and `ε > 0`, there are `C` and `N₀` such that for
every `N ≥ N₀` there are `d`, a residual vector `Δ` and local isometries with: `|d − NS| ≤ C√N`;
`Δ` has at most `2^{C√N}` Schmidt terms; `‖ψ^N − (V_A ⊗ V_B)(Φ^d ⊗ Δ)‖ < ε`; and a unit vector `w`
whose Schmidt coefficients are `2^d`-fold degenerate has fidelity `|⟨w|ψ^N⟩|² > 1 − ε` with `ψ^N`.

**Formalization Note** `O(√N)` is read as one constant `C`, chosen after `ψ` and `ε` and before
`N₀` (the page: "The actual coefficient of the √N term will depend on the value of ǫ"). `S` is the
published `WildeQIT.EntManip.entEntropy`, the entropy of `ρ^A`. The local dimensions are arbitrary
finite sets, so `Φ^d ⊗ Δ` is placed in `H_A^{⊗N} ⊗ H_B^{⊗N}` by isometries: `2^d L` need not equal
the dimension. `u₂` of Eq. (9) is the difference inside the norm. Fidelity of pure states is the
squared overlap (Jozsa, reference [11]). -/
theorem tensorPow_eq_singlets_residual_add_small {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (ψ : EuclideanSpace ℂ (a × b)) (hψ : QAlgorithms.IsState ψ) (ε : ℝ) (hε : 0 < ε) : ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ (d L : ℕ) (VA : Matrix (Fin N → a) (QAlgorithms.Qubits d × Fin L) ℂ) (VB : Matrix (Fin N → b) (QAlgorithms.Qubits d × Fin L) ℂ) (Δ : EuclideanSpace ℂ (Fin L × Fin L)), VAᴴ * VA = 1 ∧ VBᴴ * VB = 1 ∧ |(d : ℝ) - N * WildeQIT.EntManip.entEntropy (fun z => ψ z)| ≤ C * Real.sqrt N ∧ (schmidtRank Δ : ℝ) ≤ 2 ^ (C * Real.sqrt N) ∧ ‖tensorPowCut ψ N - bilocal VA VB (pairTensor (singletPow d) Δ)‖ < ε ∧ ∃ w : EuclideanSpace ℂ ((Fin N → a) × (Fin N → b)), QAlgorithms.IsState w ∧ IsSchmidtDegenerate (2 ^ d) w ∧ 1 - ε < ‖inner ℂ w (tensorPowCut ψ N)‖ ^ 2 := by sorry

end LoPopescuCC.Dilution
