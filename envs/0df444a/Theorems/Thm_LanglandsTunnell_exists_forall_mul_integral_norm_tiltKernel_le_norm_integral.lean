-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_forall_mul_integral_norm_tiltKernel_le_norm_integral
-- name    : LanglandsTunnell.exists_forall_mul_integral_norm_tiltKernel_le_norm_integral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/956dc368-445a-53ae-833a-7e0660392048
-- title:
--   Asymptotic phase coherence of the tilted Gaussian double integral
-- statement:
--   Let $a$ be a nonzero real number, let $A,B\in\mathbb{C}$, let $\tau\in\mathbb{R}$ and let $\varepsilon>0$. For $y\in\mathbb{R}$ write $S=y+i\tau$ and consider, for $w,r>0$, the integrand $$G_y(w,r)=\bigl(1+((wr)^2)^{-1}\bigr)^{-S}\,w^{A}\,r^{B}\,e^{-\pi\,(r^2+(w^2)^{-1}+a^2w^2)},$$ where the real quantities $1+((wr)^2)^{-1}$, $w$, $r$ are coerced into $\mathbb{C}$ and raised to complex powers, and the Gaussian factor is the real exponential coerced into $\mathbb{C}$. The assertion is that there exists a real threshold $R$ such that for every real $y$ with $R\le y$ one has $$(1-\varepsilon)\int_{w\in(0,\infty)}\int_{r\in(0,\infty)}\|G_y(w,r)\|\;\le\;\Bigl\|\int_{w\in(0,\infty)}\int_{r\in(0,\infty)}G_y(w,r)\Bigr\|,$$ the integrals being iterated Bochner integrals over $(0,\infty)$ in $r$ and then in $w$: the total mass of $|G_y|$ is, up to the factor $1-\varepsilon$, dominated by the absolute value of the (complex) integral of $G_y$ itself, uniformly for all sufficiently large $y$ with the imaginary part $\tau$ of the exponent held fixed.
--
--   This is the coherence statement for the archimedean double integral attached to the Gaussian torus transform: as the real part $y$ of the exponent grows, the oscillation of the integrand over the region carrying the mass becomes negligible, so no cancellation occurs and the modulus of the integral is comparable to the integral of the modulus. It is obtained by combining a concentration estimate, which confines all but an $\eta$-fraction of the mass of $|G_y|$ to a logarithmic box in $(w,r)$, with a phase estimate on such a box giving a unimodular $u$ for which $\mathrm{Re}(uG_y)$ dominates $\cos\Delta\cdot\|G_y\|$ there; it is used for the non-vanishing and the half-step bound for the Mellin transform of the Gaussian torus transform in the archimedean input to the converse theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_forall_mul_integral_norm_tiltKernel_le_norm_integral.lean

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

theorem LanglandsTunnell.exists_forall_mul_integral_norm_tiltKernel_le_norm_integral
    (a : ℝ) (ha : a ≠ 0) (A B : ℂ) (τ : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, ∀ y : ℝ, R ≤ y →
      (1 - ε) * ∫ w in Ioi (0:ℝ), ∫ r in Ioi (0:ℝ),
          ‖((1 + ((w * r) ^ 2)⁻¹ : ℝ) : ℂ) ^ (-((y : ℂ) + (τ : ℂ) * Complex.I)) * ((w : ℝ) : ℂ) ^ A * ((r : ℝ) : ℂ) ^ B *
            (Real.exp (-(Real.pi * (r ^ 2 + (w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) : ℂ)‖
        ≤ ‖∫ w in Ioi (0:ℝ), ∫ r in Ioi (0:ℝ),
          ((1 + ((w * r) ^ 2)⁻¹ : ℝ) : ℂ) ^ (-((y : ℂ) + (τ : ℂ) * Complex.I)) * ((w : ℝ) : ℂ) ^ A * ((r : ℝ) : ℂ) ^ B *
            (Real.exp (-(Real.pi * (r ^ 2 + (w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) : ℂ)‖ := by sorry
