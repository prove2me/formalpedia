-- Prove2me | Theorems.Thm_GlobalTheory_HL_ContModel_gramT_std
-- name    : GlobalTheory.HL.ContModel.gramT_std
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:05:54.801792+00:00
-- url     : https://prove2.me/theorems/48e6d550-e4f4-5cde-95b1-9393f4d18f11
-- title:
--   Cont Model: gram T std
-- statement:
--   The Cont Model construction uses the gram T std property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/NcardImageOfLe.lean#L261-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/NcardImageOfLe.lean#L261-L264

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NcardImageOfLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.ContModel
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem GlobalTheory.HL.ContModel.gramT_std (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) :
    gramT L Hm (fun a => Pi.single a 1) = Hm.transpose := by sorry
