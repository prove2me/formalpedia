-- Prove2me | Theorems.Thm_GroundTheory_Global_integral_infinitePlaceUnitsMeasure_of_isReal
-- name    : GroundTheory.Global.integral_infinitePlaceUnitsMeasure_of_isReal
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:11:22.444422+00:00
-- url     : https://prove2.me/theorems/27335c3a-13aa-5521-be49-8fb26141f565
-- title:
--   Global: integral infinite Place Units Measure of is Real
-- statement:
--   The Global construction uses the integral infinite Place Units Measure of is Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/EulerFactorsArch.lean#L86-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/EulerFactorsArch.lean#L86-L102

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeChar
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchCharsUnitary
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_Gaussian
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplex
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_EulerFactorsArch
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField InfinitePlace InfinitePlace.Completion MeasureTheory Complex ComplexConjugate
open scoped Real
open GroundTheory GroundTheory.Global
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
omit [NumberField K]

theorem GroundTheory.Global.integral_infinitePlaceUnitsMeasure_of_isReal {w : InfinitePlace K} (hw : w.IsReal)
    (g : w.Completion → ℂ) :
    ∫ a : (w.Completion)ˣ, g a ∂infinitePlaceUnitsMeasure w =
      ∫ x : ℝ, g ((isometryEquivRealOfIsReal hw).symm x) / ((|x| : ℝ) : ℂ) := by sorry
