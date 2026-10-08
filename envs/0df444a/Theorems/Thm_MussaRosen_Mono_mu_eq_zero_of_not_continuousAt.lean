-- Prove2me | Theorems.Thm_MussaRosen_Mono_mu_eq_zero_of_not_continuousAt
-- name    : MussaRosen.Mono.mu_eq_zero_of_not_continuousAt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:15:01.612358+00:00
-- url     : https://prove2.me/theorems/a682577f-7539-43c2-b226-89cadcdc6c13
-- title:
--   §4, p. 310 — μ(θ) = 0 at any θ where q(θ) jumps
-- statement:
--   Under the standing hypotheses, let $q$ be an optimal assignment and $\mu$ the marginal profit of (10). If $\underline\theta<\theta<\bar\theta$ and $q$ is discontinuous at $\theta$, then
--   $$\mu(\theta)=0 .$$
--
--   This is the step the paper uses to rule out jumps in the optimal assignment.
--
--   **Formalization Note** The next milestone shows that an optimal assignment has no interior discontinuity, so the hypothesis of this statement never holds at an optimum. The statement is nevertheless the paper's own step, and it is not trivially true without that later result.
-- source:
--   Mussa and Rosen, Monopoly and product quality, J. Econ. Theory 18 (1978), p. 310, §4, paragraph after (15)

import Mathlib
import Definitions.Def_MussaRosen_Mono_Setting

open MechanismDesign.Screening Filter Topology

namespace MussaRosen.Mono

theorem mu_eq_zero_of_not_continuousAt {θlo θhi : ℝ} (D : TypeDistribution θlo θhi)
    (hfd : DifferentiableOn ℝ D.f (Set.Icc θlo θhi))
    (C : ℝ → ℝ) (hC0 : C 0 = 0) (hCd : Differentiable ℝ C) (hCd2 : Differentiable ℝ (deriv C))
    (hC1 : ∀ q : ℝ, 0 ≤ q → 0 < deriv C q) (hC2 : ∀ q : ℝ, 0 ≤ q → 0 < deriv (deriv C) q)
    (q : ℝ → ℝ) (hq : IsOptimal D C q) :
    ∀ θ ∈ Set.Ioo θlo θhi, ¬ ContinuousAt q θ → mu D C q θ = 0 := by sorry

end MussaRosen.Mono
