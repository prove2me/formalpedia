-- Prove2me | Theorems.Thm_LindenReversibility_eq_13
-- name    : LindenReversibility.eq_13
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:19:53.369737+00:00
-- url     : https://prove2.me/theorems/f533841b-46a2-44b8-b327-ad8560ba0b0c
-- title:
--   Eq. (13): the gain in $E_r$ from one measurement by Alice is at most her entropy loss
-- statement:
--   Let $\psi$ be a unit vector of $\mathbb C^A\otimes\mathbb C^B\otimes\mathbb C^C$ and let Alice measure with a complete family $K_1,\dots,K_n$ ($\sum_k K_k^\dagger K_k = I$). Let $\varphi_k = (K_k\otimes I\otimes I)\psi$, $p_k = \|\varphi_k\|^2$ and $\psi_k = \varphi_k/\|\varphi_k\|$ (the post-measurement pure state; $0$ if $p_k = 0$). Write $\rho^{BC} = \operatorname{Tr}_A|\psi\rangle\langle\psi|$, $\rho^A = \operatorname{Tr}_{BC}|\psi\rangle\langle\psi|$, and $\rho^{BC}_k$, $\rho^A_k$ for the same marginals of $\psi_k$. Then the chain
--
--   $$
--   \sum_k p_k E_r(\rho^{BC}_k) - E_r(\rho^{BC}) \le \sum_k p_k S(\rho^{BC}_k\|\rho^{BC}) = S(\rho^{BC}) - \sum_k p_k S(\rho^{BC}_k) = S(\rho^A) - \sum_k p_k S(\rho^A_k)
--   $$
--
--   holds, as three statements:
--
--   1. $\sum_k p_k E_r(\rho^{BC}_k) \le E_r(\rho^{BC}) + \sum_k p_k S(\rho^{BC}_k\|\rho^{BC})$;
--   2. $\sum_k p_k S(\rho^{BC}_k\|\rho^{BC}) + \sum_k p_k S(\rho^{BC}_k) = S(\rho^{BC})$;
--   3. $S(\rho^{BC}) = S(\rho^A)$, and $S(\rho^{BC}_k) = S(\rho^A_k)$ for every $k$ ("the last step is valid since $\rho^{ABC}$ and $\rho^{ABC}_k$ are pure").
--
--   Here $E_r$ is the relative entropy of entanglement (11), $S(\cdot\|\cdot)$ the relative entropy (9), $S$ the von Neumann entropy, all with natural logarithms. This is the core of the bound for a step by Alice.
--
--   Differences from the source:
--   - reading: the local Hilbert spaces of Alice, Bob and Claire "including ancilla's" (dimension not stated) → arbitrary finite index types A, B, C (B, C nonempty); reason: the paper works with density matrices, a min over separable states (11) and finitely many copies of finite-dimensional systems; arbitrary finite types cover any number of copies and any ancillas
--   - generalization: a local measurement with spectral projectors P_k (followed by outcome-dependent unitaries) → any finite family K_k of operators on the acting party's system with sum_k K_k^dagger K_k = 1; reason: spectral projectors, projectors followed by unitaries, and single unitaries are such families, so the statement specializes to the paper's; the paper's argument uses only the completeness relation
--   - encoding: Alice; Bob-Claire → the first tensor factor A of A × (B × C); the second factor B × C; reason: a labelling of the factors; the other pairs follow by relabelling the parties
--   - encoding: outcome probabilities p_k and normalized post-measurement states → p_k = ‖φ_k‖² for the unnormalized branch vector φ_k and the normalized branch φ_k/‖φ_k‖ (0 if φ_k = 0); reason: for a unit vector ψ these are the paper's p_k = Tr(P_k ⊗ I ⊗ I ρ^{ABC}) and states (7); a zero-probability outcome contributes 0 to every sum, as in the paper
--   - encoding: the chain (13) as a difference of real quantities → the additive rearrangement in [0, +∞] (ℝ≥0∞); reason: every term is finite (nonnegative entropies; E_r is finite on states), so the rearranged inequality is equivalent
--   - encoding: min over separable σ in (11) → infimum over separable σ; reason: the minimum is attained (compact separable set, lower semicontinuous relative entropy), so the values agree
-- source:
--   Linden, Popescu, Schumacher, Westmoreland, Reversibility of local transformations of multiparticle entanglement, arXiv:quant-ph/9912039v1, eq. (13), p.3 (with (12))

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56
import Definitions.Def_LindenReversibility_relEntropy
import Definitions.Def_LindenReversibility_liftA
import Definitions.Def_LindenReversibility_IsKrausFamily
import Definitions.Def_LindenReversibility_erBC

open QAlgorithms (act traceLeft traceRight pureDensity)
open QAlgorithms.Papers.Independent.Information100.P56 (entropy)
open scoped Matrix ENNReal

namespace LindenReversibility

/-- Linden, Popescu, Schumacher, Westmoreland, arXiv:quant-ph/9912039v1, eq. (13), p.3: Alice
measures, with outcome probabilities `p_k` and post-measurement pure states `ρ^{ABC}_k`; then
`∑_k p_k E_r(ρ^{BC}_k) − E_r(ρ^{BC}) ≤ ∑_k p_k S(ρ^{BC}_k‖ρ^{BC}) = S(ρ^{BC}) − ∑_k p_k S(ρ^{BC}_k)
= S(ρ^A) − ∑_k p_k S(ρ^A_k)`, "the last step [being] valid since ρ^{ABC} and ρ^{ABC}_k are pure".

The three clauses are the inequality, the first equality, and the pure-state equalities giving
the second equality.

**Formalization Note.** Alice is the first factor `A`; `ρ^{BC} = Tr_A` (`traceLeft`) and
`ρ^A = Tr_{BC}` (`traceRight`). Her measurement is a complete family `K_k`
(`IsKrausFamily`). With `φ_k = (K_k ⊗ 1 ⊗ 1) ψ`, `p_k = ‖φ_k‖²` and the normalized branch is
`ψ_k = φ_k / ‖φ_k‖` (`0` when `p_k = 0`, a term that then drops out). The chain is stated in
`ℝ≥0∞` in additive form (every term is finite); the entropies are natural-log von Neumann
entropies. -/
theorem eq_13 {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype C] [DecidableEq C] [Nonempty C]
    (ψ : EuclideanSpace ℂ (A × (B × C))) (hψ : ‖ψ‖ = 1)
    {n : ℕ} (K : Fin n → Matrix A A ℂ) (hK : IsKrausFamily K) :
    let φ : Fin n → EuclideanSpace ℂ (A × (B × C)) := fun k => act (liftA (K k)) ψ
    let p : Fin n → ℝ := fun k => ‖φ k‖ ^ 2
    let ψk : Fin n → EuclideanSpace ℂ (A × (B × C)) := fun k => (‖φ k‖⁻¹ : ℝ) • φ k
    (∑ k, ENNReal.ofReal (p k) * erBC (ψk k) ≤
        erBC ψ + ∑ k, ENNReal.ofReal (p k) *
          relEntropy (traceLeft (pureDensity (ψk k))) (traceLeft (pureDensity ψ))) ∧
    (∑ k, ENNReal.ofReal (p k) *
          relEntropy (traceLeft (pureDensity (ψk k))) (traceLeft (pureDensity ψ)) +
        ∑ k, ENNReal.ofReal (p k) * ENNReal.ofReal (entropy (traceLeft (pureDensity (ψk k)))) =
      ENNReal.ofReal (entropy (traceLeft (pureDensity ψ)))) ∧
    (entropy (traceLeft (pureDensity ψ)) = entropy (traceRight (pureDensity ψ)) ∧
      ∀ k, entropy (traceLeft (pureDensity (ψk k))) =
        entropy (traceRight (pureDensity (ψk k)))) := by sorry

end LindenReversibility
