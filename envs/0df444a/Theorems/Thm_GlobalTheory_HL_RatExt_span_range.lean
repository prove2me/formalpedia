-- Prove2me | Theorems.Thm_GlobalTheory_HL_RatExt_span_range
-- name    : GlobalTheory.HL.RatExt.span_range
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:34:04.345419+00:00
-- url     : https://prove2.me/theorems/5dcb02c7-a49f-4d58-87c5-fc52040c8802
-- title:
--   Rat Ext: span range
-- statement:
--   The Rat Ext construction uses the span range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/RationalExtend.lean#L23-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/RationalExtend.lean#L23-L28

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

theorem GlobalTheory.HL.RatExt.span_range {n : ℕ} :
    Submodule.span R (Set.range fun (x : Fin n → E) (i : Fin n) => ι (x i)) = ⊤ := by sorry
