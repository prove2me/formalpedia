-- Prove2me | Theorems.Thm_MeasureTheory_integrable_mul_comp_neg_div_div_of_integrable_prod_Iio_prod_Ioi
-- name    : MeasureTheory.integrable_mul_comp_neg_div_div_of_integrable_prod_Iio_prod_Ioi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/7ec88f79-f23d-554f-b689-809209c798d7
-- title:
--   Integrability transfers under the substitution (u,v)↦(-u/t, u/v)
-- statement:
--   Let $F\colon\mathbb{R}\times\mathbb{R}\times\mathbb{R}\to\mathbb{C}$ be measurable and suppose $F$ is integrable with respect to the product measure $\mathrm{vol}|_{(0,\infty)}\otimes(\mathrm{vol}|_{(-\infty,0)}\otimes\mathrm{vol}|_{(0,\infty)})$, i.e. Lebesgue measure restricted to $(0,\infty)$ in the first variable, to $(-\infty,0)$ in the second and to $(0,\infty)$ in the third. Then the function $$p=(t,u,v)\ \longmapsto\ \frac{u}{t\,v^{2}}\cdot F\!\left(t,\,-\tfrac{u}{t},\,\tfrac{u}{v}\right),$$ where the real scalar $u/(t v^{2})$ is regarded as a complex number, is integrable with respect to the product measure $\mathrm{vol}|_{(0,\infty)}\otimes(\mathrm{vol}|_{(0,\infty)}\otimes\mathrm{vol}|_{(0,\infty)})$ on $\mathbb{R}\times\mathbb{R}\times\mathbb{R}$. Thus integrability of $F$ on $(0,\infty)\times(-\infty,0)\times(0,\infty)$ yields integrability on $(0,\infty)^{3}$ of the substituted function weighted by the Jacobian factor $u/(t v^{2})$; the measures are the restricted ones, so no condition on $F$ off these regions is imposed or used.
--
--   This is the change-of-variables comparison for the fibrewise substitution $(u,v)\mapsto(-u/t,u/v)$, which for each fixed $t>0$ is a bijection of $(0,\infty)^{2}$ onto $(-\infty,0)\times(0,\infty)$ with Jacobian factor $u/(tv^{2})$. It supplies the integrability hypothesis needed for the Fubini–Tonelli rearrangement in [`LanglandsTunnell.setIntegral_oneSided_torusPair_eq_setIntegral_fiber`](thm.html#LanglandsTunnell.setIntegral_oneSided_torusPair_eq_setIntegral_fiber).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_integrable_mul_comp_neg_div_div_of_integrable_prod_Iio_prod_Ioi.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Set

theorem MeasureTheory.integrable_mul_comp_neg_div_div_of_integrable_prod_Iio_prod_Ioi
    (F : ℝ × ℝ × ℝ → ℂ) (hFm : Measurable F)
    (hF : Integrable F ((volume.restrict (Ioi (0 : ℝ))).prod
      ((volume.restrict (Iio (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))))) :
    Integrable (fun p : ℝ × ℝ × ℝ =>
        ((p.2.1 / (p.1 * p.2.2 ^ 2) : ℝ) : ℂ) * F (p.1, -(p.2.1 / p.1), p.2.1 / p.2.2))
      ((volume.restrict (Ioi (0 : ℝ))).prod
        ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))))) := by sorry
