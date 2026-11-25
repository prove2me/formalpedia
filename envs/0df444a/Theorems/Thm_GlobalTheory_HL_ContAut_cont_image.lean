-- Prove2me | Theorems.Thm_GlobalTheory_HL_ContAut_cont_image
-- name    : GlobalTheory.HL.ContAut.cont_image
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T06:14:45.24605+00:00
-- url     : https://prove2.me/theorems/6ddb7aa1-5fb5-55ca-b665-c63159d68ba9
-- title:
--   Cont Aut: cont image
-- statement:
--   The Cont Aut construction uses the cont image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/RelVolMul.lean#L46-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/RelVolMul.lean#L46-L65

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NcardImageOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelVolMul
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.ContAut

theorem GlobalTheory.HL.ContAut.cont_image : ∀ {W : Type} [AddCommGroup W] (W0 : AddSubgroup W) (φ : W ≃+ W), (W0.map φ.toAddMonoidHom).relIndex W0 ≠ 0 → W0.relIndex (W0.map φ.toAddMonoidHom) ≠ 0 → ∀ S, IsCO W0 S → IsCO W0 (φ '' S) ∧ cont W0 (φ '' S) = relVol W0 (W0.map φ.toAddMonoidHom) * cont W0 S := by sorry
