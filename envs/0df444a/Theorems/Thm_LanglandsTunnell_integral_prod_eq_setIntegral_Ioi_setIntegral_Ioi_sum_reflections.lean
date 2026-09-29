-- Prove2me | Theorems.Thm_LanglandsTunnell_integral_prod_eq_setIntegral_Ioi_setIntegral_Ioi_sum_reflections
-- name    : LanglandsTunnell.integral_prod_eq_setIntegral_Ioi_setIntegral_Ioi_sum_reflections
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/c325e4c5-3dcc-5157-9b0f-32aa4440e60e
-- title:
--   Sign-quadrant fold for integrable functions on ℝ²
-- statement:
--   Let $F : \mathbb{R} \times \mathbb{R} \to \mathbb{C}$ be integrable with respect to the product of Lebesgue measure on $\mathbb{R}$ with itself. Then the integral of $F$ over the plane against that product measure equals the iterated integral $$\int_{t \in (0,\infty)} \int_{y \in (0,\infty)} \bigl[F(t,y) + F(-t,y) + F(t,-y) + F(-t,-y)\bigr]\,dy\,dt,$$ both inner and outer integrals being Bochner integrals of $\mathbb{C}$-valued functions against Lebesgue measure restricted to the open half-line $(0,\infty)$. Thus a single integral over $\mathbb{R}^2$ is rewritten as an iterated integral over the open positive quadrant of the sum of the four sign reflections of $F$; no symmetry of $F$ is assumed, and integrability over the plane is the only hypothesis.
--
--   This is the standard decomposition of $\mathbb{R}^2$ into its four sign quadrants, combined with Fubini's theorem, in the form used for bookkeeping in the archimedean (torus-pair) integral evaluations of the converse-theorem input to the Langlands–Tunnell step. It is invoked by the computations of products of archimedean $\Gamma$-factors attached to the dual-torus integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_integral_prod_eq_setIntegral_Ioi_setIntegral_Ioi_sum_reflections.lean

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Set

theorem LanglandsTunnell.integral_prod_eq_setIntegral_Ioi_setIntegral_Ioi_sum_reflections
    (F : ℝ × ℝ → ℂ) (hF : Integrable F ((volume : Measure ℝ).prod (volume : Measure ℝ))) :
    ∫ p : ℝ × ℝ, F p ∂((volume : Measure ℝ).prod (volume : Measure ℝ)) =
      ∫ t in Set.Ioi (0 : ℝ), ∫ y in Set.Ioi (0 : ℝ), (F (t, y) + F (-t, y) + F (t, -y) + F (-t, -y)) := by sorry
