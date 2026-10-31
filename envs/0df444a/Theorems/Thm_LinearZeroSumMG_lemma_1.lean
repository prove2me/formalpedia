-- Prove2me | Theorems.Thm_LinearZeroSumMG_lemma_1
-- name    : LinearZeroSumMG.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:52:28.809019+00:00
-- url     : https://prove2.me/theorems/12d3277f-6f52-4f05-bc1d-1354c42f3db3
-- title:
--   Lemma 1, p.7 — $Q^{\pi,\nu}_h(x,a,b)=\langle\phi(x,a,b),w^{\pi,\nu}_h\rangle$
-- statement:
--   **Lemma 1 (Linearity of the value function).** Under Assumption 1, for every pair of (measurable, stochastic, Markov) policies $(\pi,\nu)$ and every step $h\in[H]$, there is a vector $w^{\pi,\nu}_h\in\mathbb R^d$ such that
--   $$
--   Q^{\pi,\nu}_h(x,a,b)=\langle\phi(x,a,b),w^{\pi,\nu}_h\rangle\qquad\text{for all }(x,a,b)\in\mathcal S\times\mathcal A\times\mathcal A .
--   $$
--
--   This is what justifies estimating every action-value function by linear regression on the features.
--
--   Differences from the source:
--   - reading: Assumption 1's normalization ‖μ_h(𝒮)‖ ≤ √d (p.7) → ‖(∫ v dμ_h^{(i)})_{i∈[d]}‖ ≤ √d for every measurable v : 𝒮 → [−1, 1] (IsLinearMG); reason: read literally as a bound on the vector of net masses, the assumption does not give ‖∫ V dμ_h‖ ≤ H√d for |V| ≤ H, which the proofs of Lemmas 3 and 7 use, and Lemma 7 is then false (d = 3, two states, φ(s) = (0.7, 0.5, 0), φ(t) = (0.7, −0.5, 0), μ = ((δ_s+δ_t)/1.4, δ_s − δ_t, 7(δ_s − δ_t)), θ = (0, 1, 0), H = 2: ‖μ(𝒮)‖ ≈ 1.43 ≤ √3 but ‖w_1‖ ≥ 7 > 4√3); the reading implies the printed bound (v ≡ 1) and is implied by the total-variation bound
--   - encoding: feature map, policies, CCE rule and rounding with no measurability stated; finite action set → φ jointly measurable, policies measurable in the state, CCE rule and rounding rule Borel measurable, A with its discrete σ-algebra; reason: without measurability the expectations ℙ_h V and the conditional laws of the analysis are undefined; these conditions exclude only such cases
--   - encoding: V^{π,ν}_h, Q^{π,ν}_h as expected sums of rewards along a trajectory; V^{*,ν} = max_π, V^{π,*} = min_ν (p.6) → backward Bellman recursion for a fixed pair; best responses as ⨆/⨅ over measurable stochastic Markov policies; reason: for a fixed Markov policy pair the trajectory expectation equals the recursion; same instances
-- source:
--   Xie, Chen, Wang & Yang, Learning Zero-Sum Simultaneous-Move Markov Games Using Function Approximation and Correlated Equilibrium, arXiv:2002.07066v3, Lemma 1, p.7

import Mathlib
import Definitions.Def_LinearZeroSumMG_IsLinearMG
import Definitions.Def_LinearZeroSumMG_IsPolicy
import Definitions.Def_LinearZeroSumMG_Vval

open Matrix

namespace LinearZeroSumMG

/-- **Lemma 1 (Linearity of Value Function).**
Xie, Chen, Wang & Yang, *Learning Zero-Sum Simultaneous-Move Markov Games Using Function
Approximation and Correlated Equilibrium*, arXiv:2002.07066v3, Lemma 1, p.7: "Under Assumption 1, for
any policy pair `(π, ν)` and any `h ∈ [H]`, there exists a vector `w^{π,ν}_h ∈ ℝ^d` such that
`Q^{π,ν}_h(x, a, b) = ⟨φ(x, a, b), w^{π,ν}_h⟩, ∀(x, a, b) ∈ 𝒮 × 𝒜 × 𝒜`."

**Formalization Note** Policies are the measurable stochastic Markov policies of `IsPolicy`;
Assumption 1 is `IsLinearMG` (reading R1 of its normalization, which this lemma does not use). -/
theorem lemma_1 {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] [Fintype A] {d : ℕ}
    (G : MarkovGame S A) (φ : S → A → A → Fin d → ℝ) (θ : ℕ → Fin d → ℝ)
    (μ : ℕ → Fin d → MeasureTheory.SignedMeasure S) (hlin : IsLinearMG G φ θ μ)
    (π ν : ℕ → S → A → ℝ) (hπ : IsPolicy π) (hν : IsPolicy ν) (h : ℕ)
    (hh : h ∈ Finset.Icc 1 G.H) :
    ∃ w : Fin d → ℝ, ∀ x a b, Qval G π ν h x a b = φ x a b ⬝ᵥ w := by sorry

end LinearZeroSumMG
