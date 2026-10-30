-- Prove2me | Theorems.Thm_LindenReversibility_eq_15
-- name    : LindenReversibility.eq_15
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:20:15.912967+00:00
-- url     : https://prove2.me/theorems/ded4575b-35e5-4430-bed8-ded4218748f2
-- title:
--   Eq. (15): Alice's round — measurement, broadcast, outcome-dependent unitaries
-- statement:
--   Let $\psi$ be a unit vector of $\mathbb C^A\otimes\mathbb C^B\otimes\mathbb C^C$. Alice measures with a complete family $K_1,\dots,K_n$ ($\sum_k K_k^\dagger K_k = I$), announces the outcome $k$, and then Alice, Bob and Claire apply unitaries $U^A_k$, $U^B_k$, $U^C_k$ depending on $k$. Let $\varphi_k = (K_k\otimes I\otimes I)\psi$, $p_k = \|\varphi_k\|^2$, and let
--   $$
--   \tilde\psi_k = (U^A_k\otimes U^B_k\otimes U^C_k)\,\varphi_k/\|\varphi_k\|
--   $$
--   be the final branch, with marginals $\tilde\rho^{BC}_k$, $\tilde\rho^A_k$. Then
--
--   $$
--   \sum_k p_k E_r(\tilde\rho^{BC}_k) - E_r(\rho^{BC}) \le S(\rho^A) - \sum_k p_k S(\tilde\rho^A_k).
--   $$
--
--   The average increase in $E_r$ for the Bob–Claire system is no greater than the average decrease in the entropy of Alice's system.
--
--   Differences from the source:
--   - reading: the local Hilbert spaces of Alice, Bob and Claire "including ancilla's" (dimension not stated) → arbitrary finite index types A, B, C (B, C nonempty); reason: the paper works with density matrices, a min over separable states (11) and finitely many copies of finite-dimensional systems; arbitrary finite types cover any number of copies and any ancillas
--   - generalization: a local measurement with spectral projectors P_k (followed by outcome-dependent unitaries) → any finite family K_k of operators on the acting party's system with sum_k K_k^dagger K_k = 1; reason: spectral projectors, projectors followed by unitaries, and single unitaries are such families, so the statement specializes to the paper's; the paper's argument uses only the completeness relation
--   - encoding: Alice; Bob-Claire → the first tensor factor A of A × (B × C); the second factor B × C; reason: a labelling of the factors; the other pairs follow by relabelling the parties
--   - encoding: outcome probabilities p_k and normalized post-measurement states → p_k = ‖φ_k‖² for the unnormalized branch vector φ_k and the normalized branch φ_k/‖φ_k‖ (0 if φ_k = 0); reason: for a unit vector ψ these are the paper's p_k = Tr(P_k ⊗ I ⊗ I ρ^{ABC}) and states (7); a zero-probability outcome contributes 0 to every sum, as in the paper
--   - encoding: (15) as a difference of real quantities → the additive rearrangement in [0, +∞] (ℝ≥0∞); reason: every term is finite (nonnegative entropies; E_r is finite on states), so the rearranged inequality is equivalent
--   - reading: (14) printed as U^B_k ⊗ U^C_k ρ^{BC}_k ⊗ (U^C_k)^†, which is not a well-formed expression → the map ρ ↦ (U^B_k ⊗ U^C_k) ρ (U^B_k ⊗ U^C_k)^† (the unitaries act on the joint pure state); reason: the printed display omits (U^B_k)^†; the sentence after it ("if σ^{BC} is separable, then so is U ⊗ V σ^{BC} U^† ⊗ V^†") fixes the intended map
-- source:
--   Linden, Popescu, Schumacher, Westmoreland, Reversibility of local transformations of multiparticle entanglement, arXiv:quant-ph/9912039v1, eq. (15), p.3 (with (14))

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_LindenReversibility_liftA
import Definitions.Def_LindenReversibility_liftB
import Definitions.Def_LindenReversibility_liftC
import Definitions.Def_LindenReversibility_IsKrausFamily
import Definitions.Def_LindenReversibility_entA
import Definitions.Def_LindenReversibility_erBC

open QAlgorithms (act)
open scoped Matrix ENNReal

namespace LindenReversibility

/-- Linden, Popescu, Schumacher, Westmoreland, arXiv:quant-ph/9912039v1, eq. (15), p.3: Alice
measures, communicates the outcome `k`, and Bob, Claire and Alice apply unitaries
`U^B_k`, `U^C_k`, `U^A_k` depending on it (14); with `ρ̃_k` the resulting states,
`∑_k p_k E_r(ρ̃^{BC}_k) − E_r(ρ^{BC}) ≤ S(ρ^A) − ∑_k p_k S(ρ̃^A_k)`.

**Formalization Note.** Alice's measurement is a complete family `K_k` on `A`
(`IsKrausFamily`). With `φ_k = (K_k ⊗ 1 ⊗ 1) ψ` and `p_k = ‖φ_k‖²`, the final branch is
`ψ̃_k = (U^A_k ⊗ U^B_k ⊗ U^C_k) φ_k / ‖φ_k‖`. The inequality is stated in `ℝ≥0∞` in the
additive form `∑ p_k E_r(ψ̃_k) + ∑ p_k S_A(ψ̃_k) ≤ E_r(ψ) + S_A(ψ)` (every term is finite). -/
theorem eq_15 {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype C] [DecidableEq C] [Nonempty C]
    (ψ : EuclideanSpace ℂ (A × (B × C))) (hψ : ‖ψ‖ = 1)
    {n : ℕ} (K : Fin n → Matrix A A ℂ) (hK : IsKrausFamily K)
    (UA : Fin n → Matrix A A ℂ) (hUA : ∀ k, UA k ∈ Matrix.unitaryGroup A ℂ)
    (UB : Fin n → Matrix B B ℂ) (hUB : ∀ k, UB k ∈ Matrix.unitaryGroup B ℂ)
    (UC : Fin n → Matrix C C ℂ) (hUC : ∀ k, UC k ∈ Matrix.unitaryGroup C ℂ) :
    let φ : Fin n → EuclideanSpace ℂ (A × (B × C)) := fun k => act (liftA (K k)) ψ
    let p : Fin n → ℝ := fun k => ‖φ k‖ ^ 2
    let ψt : Fin n → EuclideanSpace ℂ (A × (B × C)) := fun k =>
      (‖φ k‖⁻¹ : ℝ) • act (liftA (UA k)) (act (liftB (UB k)) (act (liftC (UC k)) (φ k)))
    ∑ k, ENNReal.ofReal (p k) * erBC (ψt k) + ∑ k, ENNReal.ofReal (p k) * entA (ψt k) ≤
      erBC ψ + entA ψ := by sorry

end LindenReversibility
