-- Prove2me | Theorems.Thm_Newton_core_indicator_eLpNorm_bound
-- name    : Newton.core_indicator_eLpNorm_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:07:24.713002+00:00
-- url     : https://prove2.me/theorems/268ef3ff-f9b7-46b6-96db-0007345ff5f1
-- title:
--   Newton: core indicator e Lp Norm bound
-- statement:
--   The Newton construction uses the core indicator e Lp Norm bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/ApproximateIdentity.lean#L282-L306
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/ApproximateIdentity.lean#L282-L306

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

theorem Newton.core_indicator_eLpNorm_bound
    {p : ℝ≥0∞} {coreSet : Set (Fin n → ℝ)}
    (h_core_meas : MeasurableSet coreSet)
    {g : (Fin n → ℝ) → ℂ} {δ : ℝ}
    (h_bound :
      ∀ᵐ x ∂volume.restrict coreSet, ‖g x‖ ≤ δ) :
  eLpNorm (fun x => Set.indicator coreSet g x) p volume
    ≤ (volume coreSet) ^ (1 / p.toReal) * ENNReal.ofReal δ := by sorry
