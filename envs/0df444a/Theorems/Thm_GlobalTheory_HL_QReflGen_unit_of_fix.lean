-- Prove2me | Theorems.Thm_GlobalTheory_HL_QReflGen_unit_of_fix
-- name    : GlobalTheory.HL.QReflGen.unit_of_fix
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:06:39.554855+00:00
-- url     : https://prove2.me/theorems/d3ac6ded-a49f-46c1-9c84-d7f6b9c69709
-- title:
--   QRefl Gen: unit of fix
-- statement:
--   The QRefl Gen construction uses the unit of fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsometriesFixingSubspaceLeQuasiReflectionClosure.lean#L74-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsometriesFixingSubspaceLeQuasiReflectionClosure.lean#L74-L77

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfPerpEqBot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsometriesFixingSubspaceLeQuasiReflectionClosure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.QReflGen
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem GlobalTheory.HL.QReflGen.unit_of_fix (L : LocE F E) {z : E} (hz : L.cj z = z) (h0 : z ≠ 0) : IsUnit z := by sorry
