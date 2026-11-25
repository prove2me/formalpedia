-- Prove2me | Theorems.Thm_Newton_mollifier_converges_Lp
-- name    : Newton.mollifier_converges_Lp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:07:44.060801+00:00
-- url     : https://prove2.me/theorems/d2e3bfa9-4a23-4ae7-8b0d-4b1dbaa4e6b9
-- title:
--   Newton: mollifier converges Lp
-- statement:
--   **Mollifier convergence in Lp (general result).**
--
--   For f ∈ Lp with 1 ≤ p < ∞ and ψ an approximate identity:
--     ‖f - f * ψ_η‖_p → 0 as η → 0
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/ApproximateIdentity.lean#L740-L1277
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/ApproximateIdentity.lean#L740-L1277

import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Definitions.Def_Newton_Analysis_Convolution_Basic
import Definitions.Def_Newton_MeasureTheory_Integral_Holder
import Definitions.Def_Newton_MeasureTheory_Function_LpSpace_ContinuousDense
import Definitions.Def_Newton_Analysis_Convolution_ApproximateIdentity
set_option autoImplicit false
open MeasureTheory Complex NNReal SchwartzMap
open scoped ENNReal ContDiff Topology Pointwise
open Newton
variable {n : ℕ}

theorem Newton.mollifier_converges_Lp
    (f : (Fin n → ℝ) → ℂ)
    (ψ : (Fin n → ℝ) → ℝ)
    (p : ℝ≥0∞)
    (hp : 1 ≤ p) (hp_ne_top : p ≠ ⊤)
    (hf : MemLp f p volume)
    (hψ : IsApproximateIdentity ψ) :
    ∀ ε > 0, ∃ δ > 0, ∀ η : ℝ, 0 < η → η < δ →
      eLpNorm (fun x => f x - ∫ y, f (x - y) * (scaledMollifier ψ η y)) p volume <
        ENNReal.ofReal ε := by sorry
