-- Prove2me | Theorems.Thm_GlobalTheory_T_unitIndicatorGLBlock_isLocallyConstantCompactSupport
-- name    : GlobalTheory.T.unitIndicatorGLBlock_isLocallyConstantCompactSupport
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:00:54.212463+00:00
-- url     : https://prove2.me/theorems/7484494c-5ab6-4a87-b5ef-d5450536ea0e
-- title:
--   T: unit Indicator GLBlock is Locally Constant Compact Support
-- statement:
--   The T construction uses the unit Indicator GLBlock is Locally Constant Compact Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitIndicatorGLBlockIsLocallyConstantCompactSuppStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitIndicatorGLBlockIsLocallyConstantCompactSuppStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitIndicatorGLBlockIsLocallyConstantCompactSupp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitIndicatorGLBlockIsLocallyConstantCompactSuppStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.unitIndicatorGLBlock_isLocallyConstantCompactSupport : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F] (r : ℕ), IsTest (unitG r F) := by sorry
