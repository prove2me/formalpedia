-- Prove2me | Theorems.Thm_JHolomorphic_eLpNorm_segment_average_le
-- name    : JHolomorphic.eLpNorm_segment_average_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T20:15:10.454902+00:00
-- url     : https://prove2.me/theorems/1a3b93ca-a9a8-41c6-8bdc-18d8c3e13c69
-- title:
--   $L^q$ bound for averages of a function over segments $z+[0,1]a$
-- statement:
--   Let $E$ be a real normed space, $G:\mathbb{C}\to E$ strongly measurable, $a,c\in\mathbb{C}$, $r\in\mathbb{R}$ and $1\le q\le\infty$. Then the segment average
--   $$A(z)=\int_0^1 G(z+ta)\,dt$$
--   satisfies
--   $$\|A\|_{L^q(B(c,r))}\le\|G\|_{L^q(B(c,r+|a|))}.$$
--   It is a reusable tool for $L^q$ bounds of difference quotients in Sobolev regularity theory.
--
--   **Formalization Note** The average is the interval integral `∫ t in (0:ℝ)..1, G (z + (t:ℂ) * a)` (a Bochner integral). The norms are `eLpNorm _ q` for Lebesgue measure on $\mathbb{C}$ restricted to the open discs `ball c r` and `ball c (r + ‖a‖)`. Strong measurability of `G` is assumed on all of $\mathbb{C}$.
-- source:
--   Standard; cf. L. C. Evans, Partial Differential Equations, §5.8.2, proof of Theorem 3 (i)

import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace JHolomorphic

open MeasureTheory Metric
open scoped ENNReal

/-- For a strongly measurable `G : ℂ → E`, `a, c ∈ ℂ`, `r ∈ ℝ` and `1 ≤ q ≤ ∞`, the average
`z ↦ ∫₀¹ G (z + t a) dt` has `L^q(B(c, r))` norm at most the `L^q(B(c, r + ‖a‖))` norm of `G`. -/
theorem eLpNorm_segment_average_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : ℂ → E} (hG : StronglyMeasurable G) {q : ℝ≥0∞} (hq : 1 ≤ q) (a c : ℂ) (r : ℝ) :
    eLpNorm (fun z => ∫ t in (0:ℝ)..1, G (z + (t:ℂ) * a)) q (volume.restrict (ball c r)) ≤
      eLpNorm G q (volume.restrict (ball c (r + ‖a‖))) := by
  sorry

end JHolomorphic
