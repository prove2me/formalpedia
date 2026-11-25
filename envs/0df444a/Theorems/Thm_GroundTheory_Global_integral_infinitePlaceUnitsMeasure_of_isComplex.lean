-- Prove2me | Theorems.Thm_GroundTheory_Global_integral_infinitePlaceUnitsMeasure_of_isComplex
-- name    : GroundTheory.Global.integral_infinitePlaceUnitsMeasure_of_isComplex
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:12:59.010208+00:00
-- url     : https://prove2.me/theorems/5049ae67-3a2b-5649-a8eb-5fd57a51dec6
-- title:
--   Global: integral infinite Place Units Measure of is Complex
-- statement:
--   The Global construction uses the integral infinite Place Units Measure of is Complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/EulerFactorsArch.lean#L106-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/EulerFactorsArch.lean#L106-L125

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

theorem GroundTheory.Global.integral_infinitePlaceUnitsMeasure_of_isComplex {w : InfinitePlace K} (hw : w.IsComplex)
    (g : w.Completion → ℂ) :
    ∫ a : (w.Completion)ˣ, g a ∂infinitePlaceUnitsMeasure w =
      ∫ z : ℂ, g ((isometryEquivComplexOfIsComplex hw).symm z) / ((‖z‖ ^ 2 : ℝ) : ℂ)
        ∂complexPlaceMeasure := by sorry
