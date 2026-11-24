-- Prove2me | Theorems.Thm_GlobalTheory_JR_UnitTest_isLocallyConstant_indicator_one
-- name    : GlobalTheory.JR.UnitTest.isLocallyConstant_indicator_one
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:36:44.005721+00:00
-- url     : https://prove2.me/theorems/acab72b5-df11-4250-a5be-d3eb09e447c3
-- title:
--   Unit Test: is Locally Constant indicator one
-- statement:
--   The Unit Test construction uses the is Locally Constant indicator one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitIndicatorGLBlockIsLocallyConstantCompactSupp.lean#L7-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitIndicatorGLBlockIsLocallyConstantCompactSupp.lean#L7-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitIndicatorGLBlockIsLocallyConstantCompactSupp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.UnitTest

theorem GlobalTheory.JR.UnitTest.isLocallyConstant_indicator_one {Z : Type} [TopologicalSpace Z] {W : Set Z} (hW : IsClopen W) :
    IsLocallyConstant (W.indicator (1 : Z → ℂ)) := by sorry
