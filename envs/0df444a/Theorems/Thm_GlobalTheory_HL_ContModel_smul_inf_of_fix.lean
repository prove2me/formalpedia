-- Prove2me | Theorems.Thm_GlobalTheory_HL_ContModel_smul_inf_of_fix
-- name    : GlobalTheory.HL.ContModel.smul_inf_of_fix
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:39:43.327107+00:00
-- url     : https://prove2.me/theorems/1eb842bb-f2b3-5f26-a8aa-80f10a68f9b7
-- title:
--   Cont Model: smul inf of fix
-- statement:
--   The Cont Model construction uses the smul inf of fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/NcardImageOfLe.lean#L181-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/NcardImageOfLe.lean#L181-L196

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

theorem GlobalTheory.HL.ContModel.smul_inf_of_fix (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (Y : Submodule E (Fin n → E)) (g : fixG L Hm Y) (Λ : Submodule L.O (Fin n → E)) :
    (g • Λ) ⊓ Y.restrictScalars L.O = Λ ⊓ Y.restrictScalars L.O := by sorry
