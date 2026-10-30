-- Prove2me | Theorems.Thm_LindenReversibility_every_step
-- name    : LindenReversibility.every_step
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:19:53.733919+00:00
-- url     : https://prove2.me/theorems/4197e578-da79-403f-9d61-add12e79b325
-- title:
--   p.3 after (21): inequality (15) holds for a step by any party
-- statement:
--   Let $\psi$ be a unit vector of $\mathbb C^A\otimes\mathbb C^B\otimes\mathbb C^C$ and let one party $X\in\{\text{Alice},\text{Bob},\text{Claire}\}$ apply a complete family $K_1,\dots,K_n$ on their system ($\sum_k K_k^\dagger K_k = I$). Let $\varphi_k$ be the unnormalized branch ($K_k$ acting on $X$'s factor of $\psi$), $p_k = \|\varphi_k\|^2$ and $\psi_k = \varphi_k/\|\varphi_k\|$. Then
--
--   $$
--   \sum_k p_k\,E_r(BC)(\psi_k) - E_r(BC)(\psi) \le S(A)(\psi) - \sum_k p_k\,S(A)(\psi_k).
--   $$
--
--   The three clauses are $X$ = Alice, Bob, Claire. This is the paper's "(20) and (21) imply that (15) is true for any step in the protocol"; applied to each step of each branch it yields (22).
--
--   Differences from the source:
--   - reading: the local Hilbert spaces of Alice, Bob and Claire "including ancilla's" (dimension not stated) → arbitrary finite index types A, B, C (B, C nonempty); reason: the paper works with density matrices, a min over separable states (11) and finitely many copies of finite-dimensional systems; arbitrary finite types cover any number of copies and any ancillas
--   - encoding: Alice; Bob-Claire → the first tensor factor A of A × (B × C); the second factor B × C; reason: a labelling of the factors; the other pairs follow by relabelling the parties
--   - encoding: outcome probabilities p_k and normalized post-measurement states → p_k = ‖φ_k‖² for the unnormalized branch vector φ_k and the normalized branch φ_k/‖φ_k‖ (0 if φ_k = 0); reason: for a unit vector ψ these are the paper's p_k = Tr(P_k ⊗ I ⊗ I ρ^{ABC}) and states (7); a zero-probability outcome contributes 0 to every sum, as in the paper
--   - encoding: (15) as a difference of real quantities → the additive rearrangement in [0, +∞] (ℝ≥0∞); reason: every term is finite (nonnegative entropies; E_r is finite on states), so the rearranged inequality is equivalent
--   - generalization: a step: one party measures with spectral projectors, the outcome is broadcast, and the parties apply outcome-dependent unitaries → a step: one party applies any complete family K_k of operators on their system; unitaries are one-element families, i.e. steps of their own; reason: the paper's step is a measurement step followed by unitary steps in each branch, so the bound for it follows by applying the clauses to each of its parts; projector and unitary families are complete families
--   - generalization: steps by Alice and by Bob (the paper treats Claire's steps as Bob's) → clauses for Alice, Bob and Claire; reason: Claire's clause is Bob's with B and C exchanged; the paper says "for any step"
-- source:
--   Linden, Popescu, Schumacher, Westmoreland, Reversibility of local transformations of multiparticle entanglement, arXiv:quant-ph/9912039v1, p.3, sentence after (21)

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

/-- Linden, Popescu, Schumacher, Westmoreland, arXiv:quant-ph/9912039v1, p.3, after (21):
"(20) and (21) imply that (15) is true for any step in the protocol": whichever party acts,
`∑_k p_k E_r(ρ̃^{BC}_k) − E_r(ρ^{BC}) ≤ S(ρ^A) − ∑_k p_k S(ρ̃^A_k)`.

Clauses 1, 2, 3: the step is a measurement by Alice, Bob, Claire respectively.

**Formalization Note.** A step is a complete family `K_k` (`IsKrausFamily`) on the acting
party's system; outcome-dependent unitaries are themselves one-element steps of this kind. With
`φ_k` the unnormalized branch (`K_k` lifted to `A × (B × C)` and applied to `ψ`),
`p_k = ‖φ_k‖²` and `ψ_k = φ_k / ‖φ_k‖`, each clause is stated in `ℝ≥0∞` in the additive form
`∑ p_k E_r(ψ_k) + ∑ p_k S_A(ψ_k) ≤ E_r(ψ) + S_A(ψ)` (every term is finite). -/
theorem every_step {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype C] [DecidableEq C] [Nonempty C]
    (ψ : EuclideanSpace ℂ (A × (B × C))) (hψ : ‖ψ‖ = 1) :
    (∀ (n : ℕ) (K : Fin n → Matrix A A ℂ), IsKrausFamily K →
      let φ : Fin n → EuclideanSpace ℂ (A × (B × C)) := fun k => act (liftA (K k)) ψ
      ∑ k, ENNReal.ofReal (‖φ k‖ ^ 2) * erBC ((‖φ k‖⁻¹ : ℝ) • φ k) +
          ∑ k, ENNReal.ofReal (‖φ k‖ ^ 2) * entA ((‖φ k‖⁻¹ : ℝ) • φ k) ≤
        erBC ψ + entA ψ) ∧
    (∀ (n : ℕ) (K : Fin n → Matrix B B ℂ), IsKrausFamily K →
      let φ : Fin n → EuclideanSpace ℂ (A × (B × C)) := fun k => act (liftB (K k)) ψ
      ∑ k, ENNReal.ofReal (‖φ k‖ ^ 2) * erBC ((‖φ k‖⁻¹ : ℝ) • φ k) +
          ∑ k, ENNReal.ofReal (‖φ k‖ ^ 2) * entA ((‖φ k‖⁻¹ : ℝ) • φ k) ≤
        erBC ψ + entA ψ) ∧
    (∀ (n : ℕ) (K : Fin n → Matrix C C ℂ), IsKrausFamily K →
      let φ : Fin n → EuclideanSpace ℂ (A × (B × C)) := fun k => act (liftC (K k)) ψ
      ∑ k, ENNReal.ofReal (‖φ k‖ ^ 2) * erBC ((‖φ k‖⁻¹ : ℝ) • φ k) +
          ∑ k, ENNReal.ofReal (‖φ k‖ ^ 2) * entA ((‖φ k‖⁻¹ : ℝ) • φ k) ≤
        erBC ψ + entA ψ) := by sorry

end LindenReversibility
