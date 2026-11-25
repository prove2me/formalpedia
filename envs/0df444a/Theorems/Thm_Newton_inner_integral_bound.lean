-- Prove2me | Theorems.Thm_Newton_inner_integral_bound
-- name    : Newton.inner_integral_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:00:33.120709+00:00
-- url     : https://prove2.me/theorems/1d5cd712-23be-499a-9251-2c2e543988c4
-- title:
--   Newton: inner integral bound
-- statement:
--   Inner integral bound for fixed x
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/InnerBound.lean#L11-L960
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/InnerBound.lean#L11-L960

import Definitions.Def_Newton_Analysis_Convolution_Auxiliary
import Definitions.Def_Newton_Analysis_Convolution_InnerBound
set_option autoImplicit false
open MeasureTheory Complex NNReal
open scoped ENNReal Topology ContDiff ComplexConjugate
open Newton
variable {n : ℕ}

theorem Newton.inner_integral_bound
    (f g : (Fin n → ℝ) → ℂ)
    (p q r : ℝ≥0∞)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hp_ne_top : p ≠ ⊤) (hq_ne_top : q ≠ ⊤) (hr_ne_top : r ≠ ⊤)
    (hpqr : 1 / p + 1 / q = 1 + 1 / r)
    (hf : MemLp f p volume) (hg : MemLp g q volume)
    (x : Fin n → ℝ) :
    ∫⁻ y, ‖f y‖₊ * ‖g (x - y)‖₊ ∂volume ≤
      (∫⁻ y, ‖f y‖₊^p.toReal * ‖g (x - y)‖₊^q.toReal ∂volume)^(1/r.toReal) *
      (eLpNorm f p volume)^(1 - p/r).toReal *
      (eLpNorm g q volume)^(1 - q/r).toReal := by sorry
