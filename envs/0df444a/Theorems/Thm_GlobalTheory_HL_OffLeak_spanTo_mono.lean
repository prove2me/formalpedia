-- Prove2me | Theorems.Thm_GlobalTheory_HL_OffLeak_spanTo_mono
-- name    : GlobalTheory.HL.OffLeak.spanTo_mono
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:20:30.248605+00:00
-- url     : https://prove2.me/theorems/3b4001d9-2eeb-4d07-915c-3a6aa1b44336
-- title:
--   Off Leak: span To mono
-- statement:
--   The Off Leak construction uses the span To mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianDoubleCosetInFamilyMovedOfNotLeak.lean#L72-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianDoubleCosetInFamilyMovedOfNotLeak.lean#L72-L77

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermLevelZeroAndBoundedRepresentativesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianMovePreservesFrameLatticeLevelsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDefectClassMemTraceFirstFrameSpanStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PairingSecondTypeTestOnRepresentativesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetInFamilyMovedOfNotLeak
import Theorems.Thm_GlobalTheory_HL_EichlerUnip_spanTo_mono
import Theorems.Thm_GlobalTheory_HL_FrameOnto_spanTo_mono
import Theorems.Thm_GlobalTheory_HL_LevelRep_spanTo_mono
import Theorems.Thm_GlobalTheory_HL_MoveFacts_spanTo_mono
import Theorems.Thm_GlobalTheory_HL_TermBasic_spanTo_mono
import Theorems.Thm_GlobalTheory_HL_TraceRep_spanTo_mono
import Theorems.Thm_GlobalTheory_HL_TypeRep_spanTo_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.OffLeak
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem GlobalTheory.HL.OffLeak.spanTo_mono {L : LocE F E} {r k : ℕ} (S : Frames L r k) (g : Fin (r + 1) → S.V) {a b : ℕ}
    (h : a ≤ b) : S.spanTo g a ≤ S.spanTo g b := by sorry
