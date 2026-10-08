-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_mrt_disk_logderiv
-- name    : OAI.TwoPointCorrelations.mrt_disk_logderiv
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:21.834997+00:00
-- url     : https://prove2.me/theorems/4df363b5-c861-4213-b495-78e717fc9882
-- title:
--   Logarithmic derivative of an analytic function on the unit disc as a sum over its zeros
-- statement:
--   Let $f:\mathbb C\to\mathbb C$ be analytic at every point of the closed unit disc with $f(0)=1$, and let $B>0$ with $|f(z)|\le e^B$ for $|z|\le15/16$. Let $Z$ be the (finite, by `mrtDiskZeros_finite`) set of zeros of $f$ in the closed disc $|\rho|\le7/8$. Then for every $z$ with $|z|\le3/4$ and $f(z)\ne0$,
--
--   $$\Big|\frac{f'(z)}{f(z)}-\sum_{\rho\in Z}\frac{m_\rho}{z-\rho}\Big|\le c_L\,B,$$
--
--   where $m_\rho$ is the order of vanishing of $f$ at $\rho$ and $c_L$ = `mrtCharacterLogDerivativeConstant` $=\frac{16(4/5)^2}{(4/5-3/4)^3}+\Big(\big(\tfrac{(15/16)^2}{7/8}-\tfrac78\big)\log\tfrac{15/16}{7/8}\Big)^{-1}$.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.mrt_disk_logderiv`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Complex
open Filter
open scoped BigOperators
open scoped Classical
open scoped Topology

theorem mrt_disk_logderiv (f : ℂ → ℂ)
    (hf : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h0 : f 0 = 1) {B : ℝ} (hB : 0 < B)
    (hbound : ∀ z ∈ Metric.closedBall (0 : ℂ) (15 / 16), ‖f z‖ ≤ Real.exp B)
    {z : ℂ} (hz : ‖z‖ ≤ 3 / 4) (hn : f z ≠ 0) :
    ‖deriv f z / f z -
      ∑ ρ ∈ (mrtDiskZeros_finite f hf h0).toFinset,
        (analyticOrderAt f ρ).toNat / (z - ρ)‖ ≤
      mrtCharacterLogDerivativeConstant * B := by
  sorry

end OAI.TwoPointCorrelations
