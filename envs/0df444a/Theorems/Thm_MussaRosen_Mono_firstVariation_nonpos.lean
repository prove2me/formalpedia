-- Prove2me | Theorems.Thm_MussaRosen_Mono_firstVariation_nonpos
-- name    : MussaRosen.Mono.firstVariation_nonpos
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:14:40.916733+00:00
-- url     : https://prove2.me/theorems/9de2c086-9620-4e9c-90ae-a143cf1fdc05
-- title:
--   (9), p. 308 — at an optimum Λ(h; q) ≤ 0 for every admissible deformation h
-- statement:
--   Assume the standing hypotheses: $f$ is a positive, differentiable density on $[\underline\theta,\bar\theta]$; the cost satisfies $C(0)=0$, is twice differentiable, and $C'(q)>0$, $C''(q)>0$ for $q\ge0$. Let $q$ be an optimal assignment, and let $h$ be a deformation such that $q+h$ is admissible (nondecreasing, nonnegative and piecewise differentiable on $[\underline\theta,\bar\theta]$). Then
--   $$\Lambda(h;q)=\int_{\underline\theta}^{\bar\theta}\Bigl[\theta\,h(\theta)-\int_{\underline\theta}^{\theta}h(s)\,ds-C'(q(\theta))\,h(\theta)\Bigr]f(\theta)\,d\theta\le 0 .$$
--
--   This is the first-order necessary condition from which the paper derives every property of the optimal assignment.
--
--   **Formalization Note** The paper calls $h$ admissible when $q+h$ is piecewise differentiable and nondecreasing; the formal statement also requires $q+h\ge0$, because the feasible qualities are $q\ge0$ (p. 303) and the profit is only maximized over feasible assignments.
-- source:
--   Mussa and Rosen, Monopoly and product quality, J. Econ. Theory 18 (1978), p. 308, §4, equation (9)

import Mathlib
import Definitions.Def_MussaRosen_Mono_Setting

open MechanismDesign.Screening Filter Topology

namespace MussaRosen.Mono

theorem firstVariation_nonpos {θlo θhi : ℝ} (D : TypeDistribution θlo θhi)
    (hfd : DifferentiableOn ℝ D.f (Set.Icc θlo θhi))
    (C : ℝ → ℝ) (hC0 : C 0 = 0) (hCd : Differentiable ℝ C) (hCd2 : Differentiable ℝ (deriv C))
    (hC1 : ∀ q : ℝ, 0 ≤ q → 0 < deriv C q) (hC2 : ∀ q : ℝ, 0 ≤ q → 0 < deriv (deriv C) q)
    (q : ℝ → ℝ) (hq : IsOptimal D C q)
    (h : ℝ → ℝ) (hh : IsAdmissible θlo θhi (q + h)) :
    firstVariation D C q h ≤ 0 := by sorry

end MussaRosen.Mono
