-- Prove2me | Theorems.Thm_GroundTheory_Global_HeckeCharacter_integral_infiniteTest
-- name    : GroundTheory.Global.HeckeCharacter.integral_infiniteTest
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:15:01.322594+00:00
-- url     : https://prove2.me/theorems/4d2ef4f5-0473-4f06-b94f-438b6d1a4160
-- title:
--   Hecke Character: integral infinite Test
-- statement:
--   The Hecke Character construction uses the integral infinite Test property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/EulerFactorsArch.lean#L237-L317
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/EulerFactorsArch.lean#L237-L317

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
open GroundTheory.Global.HeckeCharacter
variable {K : Type*} [Field K] [NumberField K] (χ : HeckeCharacter K)

theorem GroundTheory.Global.HeckeCharacter.integral_infiniteTest (w : InfinitePlace K) {s : ℂ} (hs : 0 < s.re) :
    ∫ a : (w.Completion)ˣ, χ.infiniteTest w a * χ.infiniteComponent w a *
      ((‖(a : w.Completion)‖ ^ w.mult : ℝ) : ℂ) ^ s ∂infinitePlaceUnitsMeasure w =
      infiniteConst w * χ.infiniteGamma w s := by sorry
