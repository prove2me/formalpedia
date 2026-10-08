-- Prove2me | Theorems.Thm_MussaRosen_Mono_continuousOn_Ioo_of_optimal
-- name    : MussaRosen.Mono.continuousOn_Ioo_of_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:32:09.933002+00:00
-- url     : https://prove2.me/theorems/7726c23e-5b46-4ce8-8ab3-951360eebc51
-- title:
--   §4, pp. 310–311 — jumps in q(θ) are not optimal
-- statement:
--   Under the standing hypotheses, every optimal assignment $q$ is continuous at every interior type:
--   $$q\ \text{is continuous on }(\underline\theta,\bar\theta).$$
--
--   Since an optimal assignment is nondecreasing and has no jumps, it splits into intervals where $\dot q>0$ and intervals where $\dot q=0$; there are no "holes" in the spectrum of qualities offered by the monopolist.
--
--   **Formalization Note** Continuity is stated on the open interval: the values $q(\underline\theta)$ and $q(\bar\theta)$ do not affect the profit and are not determined by optimality.
-- source:
--   Mussa and Rosen, Monopoly and product quality, J. Econ. Theory 18 (1978), pp. 310–311, §4, (16) and the following paragraphs

import Mathlib
import Definitions.Def_MussaRosen_Mono_Setting

open MechanismDesign.Screening Filter Topology

namespace MussaRosen.Mono

theorem continuousOn_Ioo_of_optimal {θlo θhi : ℝ} (D : TypeDistribution θlo θhi)
    (hfd : DifferentiableOn ℝ D.f (Set.Icc θlo θhi))
    (C : ℝ → ℝ) (hC0 : C 0 = 0) (hCd : Differentiable ℝ C) (hCd2 : Differentiable ℝ (deriv C))
    (hC1 : ∀ q : ℝ, 0 ≤ q → 0 < deriv C q) (hC2 : ∀ q : ℝ, 0 ≤ q → 0 < deriv (deriv C) q)
    (q : ℝ → ℝ) (hq : IsOptimal D C q) :
    ContinuousOn q (Set.Ioo θlo θhi) := by sorry

end MussaRosen.Mono
