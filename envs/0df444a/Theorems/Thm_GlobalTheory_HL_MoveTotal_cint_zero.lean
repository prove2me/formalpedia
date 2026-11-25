-- Prove2me | Theorems.Thm_GlobalTheory_HL_MoveTotal_cint_zero
-- name    : GlobalTheory.HL.MoveTotal.cint_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:47:21.941636+00:00
-- url     : https://prove2.me/theorems/8df28eaf-a1cd-4156-834e-42ecc11ee6cc
-- title:
--   Move Total: cint zero
-- statement:
--   The Move Total construction uses the cint zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianMovesTotalMeasureEstimates.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianMovesTotalMeasureEstimates.lean#L25-L27

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NoLeak
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameMoveCharacterNeOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralProdFubiniStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralLinearPositiveNormBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexIntegrableShareTopLevelVectorsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerMoveScalarFibreMeasureOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermIntegralNearOneBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsFineSubgroupMovesAtLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianMovesTotalMeasureEstimates
import Theorems.Thm_GlobalTheory_IdxInt_Lin_cint_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.MoveTotal
open GlobalTheory.HL.Eichler GlobalTheory.HL.FrameOnto
variable {W W₁ W₂ W₃ : Type} [AddCommGroup W] [AddCommGroup W₁] [AddCommGroup W₂] [AddCommGroup W₃]

theorem GlobalTheory.HL.MoveTotal.cint_zero (A : AddSubgroup W) : cint A (fun _ => (0 : ℂ)) = 0 := by sorry
