-- Prove2me | Theorems.Thm_LinearZeroSumMG_lemma_7
-- name    : LinearZeroSumMG.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:52:10.163602+00:00
-- url     : https://prove2.me/theorems/f88697ea-27fa-480d-92a7-4dd9b3f8cac9
-- title:
--   Lemma 7, p.28 — $\|w^{\pi,\nu}_h\|\le2H\sqrt d$ for $w^{\pi,\nu}_h=\theta_h+\int V^{\pi,\nu}_{h+1}\,\mathrm d\mu_h$
-- statement:
--   **Lemma 7 (True coefficients are bounded).** Under Assumption 1, for every pair of (measurable, stochastic, Markov) policies $(\pi,\nu)$ and every step $h\in[H]$, the vector
--   $$
--   w^{\pi,\nu}_h=\theta_h+\int V^{\pi,\nu}_{h+1}(x')\,\mathrm d\mu_h(x')\in\mathbb R^d
--   $$
--   (the vector constructed in the proof of Lemma 1, with $\int V\,\mathrm d\mu_h=(\int V\,\mathrm d\mu^{(i)}_h)_{i\in[d]}$) represents the action-value function, $Q^{\pi,\nu}_h(x,a,b)=\langle\phi(x,a,b),w^{\pi,\nu}_h\rangle$ for all $(x,a,b)$, and satisfies
--   $$
--   \|w^{\pi,\nu}_h\|\le2H\sqrt d .
--   $$
--
--   This bounds the bias term $q_1$ in the least-squares error analysis (Lemma 3).
--
--   Differences from the source:
--   - reading: Assumption 1's normalization ‖μ_h(𝒮)‖ ≤ √d (p.7) → ‖(∫ v dμ_h^{(i)})_{i∈[d]}‖ ≤ √d for every measurable v : 𝒮 → [−1, 1] (IsLinearMG); reason: read literally as a bound on the vector of net masses, the assumption does not give ‖∫ V dμ_h‖ ≤ H√d for |V| ≤ H, which the proofs of Lemmas 3 and 7 use, and Lemma 7 is then false (d = 3, two states, φ(s) = (0.7, 0.5, 0), φ(t) = (0.7, −0.5, 0), μ = ((δ_s+δ_t)/1.4, δ_s − δ_t, 7(δ_s − δ_t)), θ = (0, 1, 0), H = 2: ‖μ(𝒮)‖ ≈ 1.43 ≤ √3 but ‖w_1‖ ≥ 7 > 4√3); the reading implies the printed bound (v ≡ 1) and is implied by the total-variation bound
--   - reading: "the linear coefficient" of Q^{π,ν}_h → the vector θ_h + ∫ V^{π,ν}_{h+1} dμ_h of Lemma 1's proof, shown both to represent Q^{π,ν}_h and to satisfy the bound; reason: the proof solves for exactly this vector, "Assuming that {φ(x, a, b)} spans ℝ^d"; with the vector named, the spanning assumption is unnecessary and is not a hypothesis
--   - encoding: feature map, policies, CCE rule and rounding with no measurability stated; finite action set → φ jointly measurable, policies measurable in the state, CCE rule and rounding rule Borel measurable, A with its discrete σ-algebra; reason: without measurability the expectations ℙ_h V and the conditional laws of the analysis are undefined; these conditions exclude only such cases
--   - encoding: V^{π,ν}_h, Q^{π,ν}_h as expected sums of rewards along a trajectory; V^{*,ν} = max_π, V^{π,*} = min_ν (p.6) → backward Bellman recursion for a fixed pair; best responses as ⨆/⨅ over measurable stochastic Markov policies; reason: for a fixed Markov policy pair the trajectory expectation equals the recursion; same instances
-- source:
--   Xie, Chen, Wang & Yang, Learning Zero-Sum Simultaneous-Move Markov Games Using Function Approximation and Correlated Equilibrium, arXiv:2002.07066v3, Lemma 7, p.28; Lemma 1's proof, p.7

import Mathlib
import Definitions.Def_LinearZeroSumMG_IsLinearMG
import Definitions.Def_LinearZeroSumMG_IsPolicy
import Definitions.Def_LinearZeroSumMG_Vval

open Matrix

namespace LinearZeroSumMG

/-- **Lemma 7 (True Coefficients Are Bounded).**
Xie, Chen, Wang & Yang, *Learning Zero-Sum Simultaneous-Move Markov Games Using Function
Approximation and Correlated Equilibrium*, arXiv:2002.07066v3, Lemma 7, p.28: "Under Assumption 1, for
each policy pair `(π, ν)` of P1 and P2, the linear coefficient of their action-value function
`Q^{π,ν}_h(x, a, b) = ⟨φ(x, a, b), w^{π,ν}_h⟩` satisfies `‖w^{π,ν}_h‖ ≤ 2H√d, ∀h ∈ [H]`."

With `w^{π,ν}_h := θ_h + ∫ V^{π,ν}_{h+1}(x') dμ_h(x')` (the vector constructed in the proof of Lemma 1,
p.7), both `Q^{π,ν}_h(x, a, b) = ⟨φ(x, a, b), w^{π,ν}_h⟩` for all `(x, a, b)` and `‖w^{π,ν}_h‖ ≤ 2H√d`,
for every step `h ∈ [1, H]` and every measurable policy pair.

**Formalization Note**
- "The linear coefficient" is read as the vector of Lemma 1's proof (the stronger reading; the
  proof's "Assuming that `{φ(x, a, b)}` spans `ℝ^d`" is then not needed and is not a hypothesis).
- `∫ V dμ_h` is the vector `(∫ V dμ_h^{(i)})_{i∈[d]}`, each integral through the Jordan decomposition.
- The bound relies on Assumption 1 as read in `IsLinearMG` (R1); under the literal net-mass reading
  of `‖μ_h(𝒮)‖ ≤ √d` it fails. -/
theorem lemma_7 {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] [Fintype A] {d : ℕ}
    (G : MarkovGame S A) (φ : S → A → A → Fin d → ℝ) (θ : ℕ → Fin d → ℝ)
    (μ : ℕ → Fin d → MeasureTheory.SignedMeasure S) (hlin : IsLinearMG G φ θ μ)
    (π ν : ℕ → S → A → ℝ) (hπ : IsPolicy π) (hν : IsPolicy ν) (h : ℕ)
    (hh : h ∈ Finset.Icc 1 G.H) :
    (∀ x a b, Qval G π ν h x a b =
        φ x a b ⬝ᵥ (θ h + fun i => sIntegral (Vval G π ν (h + 1)) (μ h i))) ∧
      ApproxVI.euclNorm (θ h + fun i => sIntegral (Vval G π ν (h + 1)) (μ h i)) ≤
        2 * G.H * Real.sqrt d := by sorry

end LinearZeroSumMG
