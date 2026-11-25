-- Prove2me | Theorems.Thm_GlobalTheory_HL_RatExt_single_comp
-- name    : GlobalTheory.HL.RatExt.single_comp
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:33:49.900851+00:00
-- url     : https://prove2.me/theorems/e0acfe5e-d751-47c6-ab67-42c34f391a5a
-- title:
--   Rat Ext: single comp
-- statement:
--   The Rat Ext construction uses the single comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/RationalExtend.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/RationalExtend.lean#L16-L21

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.RatExt
variable {E R : Type} [Field E] [CommRing R] (ι : E →+* R)

theorem GlobalTheory.HL.RatExt.single_comp {n : ℕ} (i : Fin n) :
    (fun j => ι ((Pi.single i 1 : Fin n → E) j)) = (Pi.single i 1 : Fin n → R) := by sorry
