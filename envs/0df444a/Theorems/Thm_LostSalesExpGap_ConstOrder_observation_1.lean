-- Prove2me | Theorems.Thm_LostSalesExpGap_ConstOrder_observation_1
-- name    : LostSalesExpGap.ConstOrder.observation_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:10:57.922231+00:00
-- url     : https://prove2.me/theorems/62dda71d-73b7-4fdd-98f9-8e86a0581464
-- title:
--   Observation 1, p. 10 — 𝔣_d is jointly convex, and the resulting Jensen bound on E[𝓘*]
-- statement:
--   Fix $L\ge1$. For $\mathbf d\in\mathbb R^L$ and $\chi_1,\dots,\chi_L,I\in\mathbb R$ let
--   $$
--   \mathfrak f_{\mathbf d}(\chi_1,\dots,\chi_L,I)=\max_{j=0,\dots,L}\Big(\sum_{i=1}^j(\chi_{L+1-i}-d_{L+1-i})+\delta_{j,L}I\Big).
--   $$
--   1. For each fixed $\mathbf d$, $\mathfrak f_{\mathbf d}$ is jointly convex on $\mathbb R^{L+1}$.
--   2. Let $D_1,D_2,\dots$ be i.i.d. nonnegative demands with finite mean, and let $(\boldsymbol\chi^*,\mathcal I^*)$ be a random vector, independent of the demands, such that (i) it is nonnegative with probability one and has finite mean; (ii) $\mathbb E[\mathcal I^*]=\mathbb E\big[\mathfrak f_{(D_1,\dots,D_L)}(\boldsymbol\chi^*,\mathcal I^*)\big]$; (iii) $\mathbb E[\chi^*_i]=\mathbb E[\chi^*_1]\le\mathbb E[D]$ for all $i$. Then
--   $$
--   \mathbb E[\mathcal I^*]\ge\mathbb E\Big[\max_{j=0,\dots,L}\Big(j\,\mathbb E[\chi^*_1]-\sum_{i=1}^jD_i+\delta_{j,L}\mathbb E[\mathcal I^*]\Big)\Big].
--   $$
--
--   Conditions (i)–(iii) are those of the paper's Theorem 2, which constructs such a vector from a stationary optimal policy; this observation is how the optimal policy is compared with the constant-order policy ordering $\mathbb E[\chi^*_1]$.
--
--   **Formalization Note** The law of $(\boldsymbol\chi^*,\mathcal I^*)$ is an arbitrary probability measure $\nu$ on $\mathbb R^L\times\mathbb R$ satisfying (i)–(iii) as hypotheses; independence from the demands is the product measure $\nu\otimes\mathcal D^{\otimes\mathbb N}$. Theorem 2 itself is not part of this mission.
-- source:
--   Xin, Goldberg, Optimality gap of constant-order policies decays exponentially in the lead time for lost sales models, arXiv:1409.1499v2, Observation 1, p. 10 (with Theorem 2.(i)–(iii), pp. 9–10)

import Mathlib
import Definitions.Def_LostSalesExpGap_ConstOrder_ConstantOrder

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace LostSalesExpGap.ConstOrder

/-- Observation 1, p. 10. (a) For each `d ∈ ℝ^L`, `𝔣_d(χ_1, …, χ_L, I)` is jointly convex on
`ℝ^{L+1}`. (b) For every law `ν` of `(χ*, 𝓘*)` with Theorem 2.(i)–(iii) (nonnegative, finite mean,
independent of the demands, `E[𝓘*] = E[𝔣_{(D_1,…,D_L)}(χ*, 𝓘*)]`, `E[χ*_i] = E[χ*_1] ≤ E[D]`),
`E[𝓘*] ≥ E[max_{j=0,…,L} (j E[χ*_1] − Σ_{i=1}^j D_i + δ_{j,L} E[𝓘*])]`. -/
theorem observation_1 (P : CappedBaseStock.DemandLaw) (L : ℕ) (hL : 1 ≤ L) :
    (∀ d : Fin L → ℝ, ConvexOn ℝ Set.univ (fun v : (Fin L → ℝ) × ℝ => fObs L d v.1 v.2)) ∧
    (∀ ν : Measure ((Fin L → ℝ) × ℝ), IsProbabilityMeasure ν →
      (∀ᵐ v ∂ν, (∀ i, 0 ≤ v.1 i) ∧ 0 ≤ v.2) →
      (∀ i, Integrable (fun v : (Fin L → ℝ) × ℝ => v.1 i) ν) →
      Integrable (fun v : (Fin L → ℝ) × ℝ => v.2) ν →
      ∫ v, v.2 ∂ν =
        ∫ w, fObs L (firstDemands L w.2) w.1.1 w.1.2
          ∂(ν.prod (CappedBaseStock.demandPathLaw P)) →
      (∀ i, ∫ v, v.1 i ∂ν = ∫ v, v.1 ⟨0, hL⟩ ∂ν) →
      ∫ v, v.1 ⟨0, hL⟩ ∂ν ≤ CappedBaseStock.mean P →
      ∫ d, (Finset.range (L + 1)).sup' Finset.nonempty_range_add_one (fun j =>
          (j : ℝ) * ∫ v, v.1 ⟨0, hL⟩ ∂ν - ∑ i ∈ Finset.Icc 1 j, (d (i - 1) : ℝ) +
            if j = L then ∫ v, v.2 ∂ν else 0) ∂CappedBaseStock.demandPathLaw P
        ≤ ∫ v, v.2 ∂ν) := by sorry

end LostSalesExpGap.ConstOrder
