-- Prove2me | Theorems.Thm_MussaRosen_Mono_mu_eq_zero_of_deriv_pos
-- name    : MussaRosen.Mono.mu_eq_zero_of_deriv_pos
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:14:57.360982+00:00
-- url     : https://prove2.me/theorems/37a92ccd-b4e7-44e4-937b-0cf1d8a612d8
-- title:
--   (15), p. 310 — μ(θ) = 0 wherever q̇(θ) > 0
-- statement:
--   Under the standing hypotheses, let $q$ be an optimal assignment and $\mu$ the marginal profit of (10). If $\underline\theta<\theta<\bar\theta$ and $q$ is differentiable at $\theta$ with $\dot q(\theta)>0$, then
--   $$\mu(\theta)=0 .$$
--
--   Together with (13), this pins down the optimal assignment on every interval where it is strictly increasing.
-- source:
--   Mussa and Rosen, Monopoly and product quality, J. Econ. Theory 18 (1978), p. 310, §4, condition (15)

import Mathlib
import Definitions.Def_MussaRosen_Mono_Setting

open MechanismDesign.Screening Filter Topology

namespace MussaRosen.Mono

theorem mu_eq_zero_of_deriv_pos {θlo θhi : ℝ} (D : TypeDistribution θlo θhi)
    (hfd : DifferentiableOn ℝ D.f (Set.Icc θlo θhi))
    (C : ℝ → ℝ) (hC0 : C 0 = 0) (hCd : Differentiable ℝ C) (hCd2 : Differentiable ℝ (deriv C))
    (hC1 : ∀ q : ℝ, 0 ≤ q → 0 < deriv C q) (hC2 : ∀ q : ℝ, 0 ≤ q → 0 < deriv (deriv C) q)
    (q : ℝ → ℝ) (hq : IsOptimal D C q) :
    ∀ θ ∈ Set.Ioo θlo θhi, ∀ d : ℝ, 0 < d → HasDerivAt q d θ → mu D C q θ = 0 := by sorry

end MussaRosen.Mono
