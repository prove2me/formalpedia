-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_logBox_mul_setIntegral_le_setIntegral_tiltKernel
-- name    : LanglandsTunnell.exists_logBox_mul_setIntegral_le_setIntegral_tiltKernel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/c5eb9e88-43af-5797-8c42-4a4136673bc8
-- title:
--   Concentration of the tilted kernel on a log-box
-- statement:
--   Let $a$ be a nonzero real number, let $\alpha,\beta$ be real, and let $\eta,\delta$ be positive reals. Write
--   $$T_y(w,r)=\bigl(1+((wr)^2)^{-1}\bigr)^{-y}\,w^{\alpha}r^{\beta}\,e^{-\pi\left(r^{2}+(w^{2})^{-1}+a^{2}w^{2}\right)}.$$
--   The assertion is that there exists a real $R$ such that for every real $y$ with $R\le y$ one can find reals $\ell_w,\ell_r$ with two properties: first, $y^{1/4}\le \exp(\ell_w+\ell_r)$ (the real power $y^{1/4}$ being `Real.rpow`); second, the concentration inequality
--   $$(1-\eta)\int_{w\in(0,\infty)}\int_{r\in(0,\infty)}T_y(w,r)\;\le\;\int_{w\in[e^{\ell_w-\delta},\,e^{\ell_w+\delta}]}\ \int_{r\in[e^{\ell_r-\delta},\,e^{\ell_r+\delta}]}T_y(w,r),$$
--   where the inner and outer integrals are Bochner integrals against Lebesgue measure over the indicated sets (open rays $\mathrm{Ioi}\,0$ on the left, closed intervals $\mathrm{Icc}$ on the right). Thus, up to the fraction $\eta$, all of the mass of $T_y$ sits on a box of fixed log-side $2\delta$ in each of $w$ and $r$, whose centres may be chosen so that the product $e^{\ell_w}e^{\ell_r}$ is at least $y^{1/4}$.
--
--   This is the two-dimensional Laplace-type concentration step for the tilted kernel occurring in the archimedean estimates of the Langlands–Tunnell input: a positive integrand is shown to concentrate, for large $y$, on a log-box of fixed log-width whose centre escapes to infinity at rate at least $y^{1/4}$. It is used by [`LanglandsTunnell.exists_forall_mul_integral_norm_tiltKernel_le_norm_integral`](thm.html#LanglandsTunnell.exists_forall_mul_integral_norm_tiltKernel_le_norm_integral), where the lower bound $e^{\ell_w+\ell_r}\ge y^{1/4}$ is what allows the oscillating factor to be controlled on the box.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_logBox_mul_setIntegral_le_setIntegral_tiltKernel.lean

import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Set

theorem LanglandsTunnell.exists_logBox_mul_setIntegral_le_setIntegral_tiltKernel
    (a : ℝ) (ha : a ≠ 0) (α β : ℝ) (η δ : ℝ) (hη : 0 < η) (hδ : 0 < δ) :
    ∃ R : ℝ, ∀ y : ℝ, R ≤ y → ∃ ℓw ℓr : ℝ, y ^ ((1:ℝ) / 4) ≤ Real.exp (ℓw + ℓr) ∧
      (1 - η) * ∫ w in Ioi (0:ℝ), ∫ r in Ioi (0:ℝ),
          (1 + ((w * r) ^ 2)⁻¹) ^ (-y) * w ^ α * r ^ β * Real.exp (-(Real.pi * (r ^ 2 + (w ^ 2)⁻¹ + a ^ 2 * w ^ 2)))
        ≤ ∫ w in Icc (Real.exp (ℓw - δ)) (Real.exp (ℓw + δ)), ∫ r in Icc (Real.exp (ℓr - δ)) (Real.exp (ℓr + δ)),
          (1 + ((w * r) ^ 2)⁻¹) ^ (-y) * w ^ α * r ^ β * Real.exp (-(Real.pi * (r ^ 2 + (w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) := by sorry
