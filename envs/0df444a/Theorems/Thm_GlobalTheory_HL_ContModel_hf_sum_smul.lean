-- Prove2me | Theorems.Thm_GlobalTheory_HL_ContModel_hf_sum_smul
-- name    : GlobalTheory.HL.ContModel.hf_sum_smul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:06:10.527803+00:00
-- url     : https://prove2.me/theorems/0bc1dd93-7918-46f5-bfe5-4b7e6df80a73
-- title:
--   Cont Model: hf sum smul
-- statement:
--   The Cont Model construction uses the hf sum smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/NcardImageOfLe.lean#L141-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/NcardImageOfLe.lean#L141-L158

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

theorem GlobalTheory.HL.ContModel.hf_sum_smul (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (x : Fin m → Fin n → E)
    (c d : Fin m → E) :
    hf L Hm (∑ i, c i • x i) (∑ k, d k • x k) = ∑ i, ∑ k, L.cj (d k) * hf L Hm (x i) (x k) * c i := by sorry
