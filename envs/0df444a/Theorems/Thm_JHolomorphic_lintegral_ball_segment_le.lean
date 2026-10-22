-- Prove2me | Theorems.Thm_JHolomorphic_lintegral_ball_segment_le
-- name    : JHolomorphic.lintegral_ball_segment_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T20:10:21.819988+00:00
-- url     : https://prove2.me/theorems/647f8f88-1238-479d-820d-47aec653b3e7
-- title:
--   Integrals of translates along a segment over a disc are bounded by the integral over the enlarged disc
-- statement:
--   Let $H:\mathbb{C}\to[0,\infty]$ be measurable, let $a,c\in\mathbb{C}$ and $r\in\mathbb{R}$. Then
--   $$\int_{B(c,r)}\int_{(0,1]} H(z+ta)\,dt\,dz\;\le\;\int_{B(c,r+|a|)} H(w)\,dw.$$
--   This is the integrated form of the statement that averaging over the segments $z+[0,1]a$ moves mass from the disc $B(c,r)$ only into the larger disc $B(c,r+|a|)$; it is used for $L^q$ bounds of such averages.
--
--   **Formalization Note** The integrals are lower Lebesgue integrals (`∫⁻`) for Lebesgue measure on $\mathbb{C}$ restricted to the open disc `ball c r`, Lebesgue measure on $\mathbb{R}$ restricted to `Set.Ioc 0 1`, and Lebesgue measure on $\mathbb{C}$ restricted to `ball c (r + ‖a‖)`. If $r\le 0$ the left side is $0$.
-- source:
--   Standard (Lebesgue integration, translation invariance).

import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Prod

namespace JHolomorphic

open MeasureTheory Metric
open scoped ENNReal

/-- For a measurable `H : ℂ → [0, ∞]`, `a, c ∈ ℂ` and `r ∈ ℝ`, the integral over `z ∈ B(c, r)` of the
integral over `t ∈ (0, 1]` of `H (z + t a)` is at most the integral of `H` over `B(c, r + ‖a‖)`. -/
theorem lintegral_ball_segment_le (H : ℂ → ℝ≥0∞) (hH : Measurable H) (a c : ℂ) (r : ℝ) :
    ∫⁻ z in ball c r, ∫⁻ t in Set.Ioc (0:ℝ) 1, H (z + (t:ℂ) * a) ≤
      ∫⁻ w in ball c (r + ‖a‖), H w := by
  sorry

end JHolomorphic
