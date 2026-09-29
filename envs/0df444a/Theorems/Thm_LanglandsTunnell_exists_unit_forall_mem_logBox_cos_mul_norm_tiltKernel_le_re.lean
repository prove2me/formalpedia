-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_unit_forall_mem_logBox_cos_mul_norm_tiltKernel_le_re
-- name    : LanglandsTunnell.exists_unit_forall_mem_logBox_cos_mul_norm_tiltKernel_le_re
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/ca5e458a-b916-511e-8c79-bd7a3578182e
-- title:
--   Phase coherence for v^{-S}w^Ar^B on a logarithmic box
-- statement:
--   Let $S,A,B\in\mathbb C$ and let $\delta,\ell_w,\ell_r\in\mathbb R$ with $\delta\ge 0$, and put $$\Delta=(|\operatorname{Im}A|+|\operatorname{Im}B|)\,\delta+|\operatorname{Im}S|\,e^{4\delta}e^{-2(\ell_w+\ell_r)}.$$ Assume $\Delta\le\pi$. Then there exists $u\in\mathbb C$ with $\lVert u\rVert=1$ such that for all real numbers $w,r,M$ with $M\ge 0$, $w\in[e^{\ell_w-\delta},e^{\ell_w+\delta}]$ and $r\in[e^{\ell_r-\delta},e^{\ell_r+\delta}]$, writing $$F=\bigl(1+((wr)^2)^{-1}\bigr)^{-S}\,w^{A}\,r^{B}\,M,$$ where the powers are the complex power function applied to the real bases $1+((wr)^2)^{-1}$, $w$, $r$ regarded as complex numbers and $M$ enters as a complex scalar, one has $$\cos(\Delta)\cdot\lVert F\rVert\le \operatorname{Re}(u\,F).$$ Thus a single unimodular constant $u$, independent of $w$, $r$ and $M$, rotates $F$ so that its real part captures the proportion $\cos\Delta$ of its modulus uniformly over the box.
--
--   This is the pointwise phase-coherence estimate for the tilted kernel $(1+(wr)^{-2})^{-S}w^{A}r^{B}$ on a box of side $2\delta$ in the logarithmic coordinates $\log w$, $\log r$: on such a box the argument of the kernel varies by at most $\Delta$. It is the hypothesis consumed by [`LanglandsTunnell.exists_forall_mul_integral_norm_tiltKernel_le_norm_integral`](thm.html#LanglandsTunnell.exists_forall_mul_integral_norm_tiltKernel_le_norm_integral), where coherence of the phase on a window is turned into a lower bound for the norm of an integral in terms of the integral of the norm.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_unit_forall_mem_logBox_cos_mul_norm_tiltKernel_le_re.lean

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

theorem LanglandsTunnell.exists_unit_forall_mem_logBox_cos_mul_norm_tiltKernel_le_re
    (S A B : ℂ) (δ ℓw ℓr : ℝ) (hδ : 0 ≤ δ)
    (hΔ : ((abs A.im) + (abs B.im)) * δ + (abs S.im) * Real.exp (4 * δ) * Real.exp (-(2 * (ℓw + ℓr))) ≤ Real.pi) :
    ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ (w r M : ℝ), 0 ≤ M →
      w ∈ Icc (Real.exp (ℓw - δ)) (Real.exp (ℓw + δ)) → r ∈ Icc (Real.exp (ℓr - δ)) (Real.exp (ℓr + δ)) →
      Real.cos (((abs A.im) + (abs B.im)) * δ + (abs S.im) * Real.exp (4 * δ) * Real.exp (-(2 * (ℓw + ℓr)))) *
          ‖((1 + ((w * r) ^ 2)⁻¹ : ℝ) : ℂ) ^ (-S) * ((w : ℝ) : ℂ) ^ A * ((r : ℝ) : ℂ) ^ B * (M : ℂ)‖
        ≤ (u * (((1 + ((w * r) ^ 2)⁻¹ : ℝ) : ℂ) ^ (-S) * ((w : ℝ) : ℂ) ^ A * ((r : ℝ) : ℂ) ^ B * (M : ℂ))).re := by sorry
