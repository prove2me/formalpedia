-- Prove2me | Theorems.Thm_MussaRosen_Mono_not_bunched_at_top
-- name    : MussaRosen.Mono.not_bunched_at_top
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:33:58.342098+00:00
-- url     : https://prove2.me/theorems/ef3defdd-1c6b-449d-b253-735f1f1e09b7
-- title:
--   §4, pp. 311–312 — θ^v < θ̄: no bunch at the top
-- statement:
--   Under the standing hypotheses, let $q$ be an optimal assignment and assume $C'(0)<\bar\theta$. Then $q$ is not constant on any interval $(\theta^u,\bar\theta)$ with $\theta^u<\bar\theta$: for every $\theta^u<\bar\theta$ and every constant $c$, there is $\theta\in(\theta^u,\bar\theta)$ with $q(\theta)\ne c$.
--
--   The monopolist always differentiates among the customers with the largest valuations of quality.
--
--   **Formalization Note** The hypothesis $C'(0)<\bar\theta$ says that the top type buys under competition. The paper presupposes that the monopolist serves an interval $[\theta^*,\bar\theta]$ with $\theta^*<\bar\theta$ (p. 306); without it the assignment $q\equiv0$ would be a bunch at the top.
-- source:
--   Mussa and Rosen, Monopoly and product quality, J. Econ. Theory 18 (1978), pp. 311–312, §4, last paragraph of case (ii)

import Mathlib
import Definitions.Def_MussaRosen_Mono_Setting

open MechanismDesign.Screening Filter Topology

namespace MussaRosen.Mono

theorem not_bunched_at_top {θlo θhi : ℝ} (D : TypeDistribution θlo θhi)
    (hfd : DifferentiableOn ℝ D.f (Set.Icc θlo θhi))
    (C : ℝ → ℝ) (hC0 : C 0 = 0) (hCd : Differentiable ℝ C) (hCd2 : Differentiable ℝ (deriv C))
    (hC1 : ∀ q : ℝ, 0 ≤ q → 0 < deriv C q) (hC2 : ∀ q : ℝ, 0 ≤ q → 0 < deriv (deriv C) q)
    (q : ℝ → ℝ) (hq : IsOptimal D C q) :
    deriv C 0 < θhi → ∀ θu < θhi, ∀ c : ℝ, ¬ ∀ θ ∈ Set.Ioo θu θhi, q θ = c := by sorry

end MussaRosen.Mono
