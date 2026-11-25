-- Prove2me | Theorems.Thm_GlobalTheory_HL_MoveTotal_triple
-- name    : GlobalTheory.HL.MoveTotal.triple
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:38:43.133822+00:00
-- url     : https://prove2.me/theorems/8970529f-71ff-4a3c-92a9-6d6677d7d0af
-- title:
--   Move Total: triple
-- statement:
--   The Move Total construction uses the triple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianMovesTotalMeasureEstimates.lean#L43-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianMovesTotalMeasureEstimates.lean#L43-L92

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

theorem GlobalTheory.HL.MoveTotal.triple (A₁ : AddSubgroup W₁) (A₂ : AddSubgroup W₂) (A₃ : AddSubgroup W₃) (P : W₁ → Prop)
    (Q Z : W₂ → Prop) (R : W₂ → W₃ → Prop) (M : W₁ × W₂ × W₃ → Prop)
    (hM : ∀ b u t, M (b, u, t) ↔ P b ∧ Q u ∧ R u t)
    (h1 : ∀ u, Z u → cint A₃ (ind (R u)) = 1) (h2 : ∀ u, (∃ t, R u t) → Z u) (g : W₁ → W₂ → ℂ)
    (hn : Nice (A₁.prod (A₂.prod A₃)) (fun w => ind M w * g w.1 w.2.1)) :
    Nice A₁ (fun b => ind P b * cint A₂ (fun u => ind (fun u => Q u ∧ Z u) u * g b u)) ∧
    cint (A₁.prod (A₂.prod A₃)) (fun w => ind M w * g w.1 w.2.1) =
      cint A₁ (fun b => ind P b * cint A₂ (fun u => ind (fun u => Q u ∧ Z u) u * g b u)) := by sorry
