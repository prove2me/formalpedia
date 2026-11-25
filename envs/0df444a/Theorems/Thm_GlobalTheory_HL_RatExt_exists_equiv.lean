-- Prove2me | Theorems.Thm_GlobalTheory_HL_RatExt_exists_equiv
-- name    : GlobalTheory.HL.RatExt.exists_equiv
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:33:41.076634+00:00
-- url     : https://prove2.me/theorems/59d06053-8c02-4ae9-821f-d53e3844c2d3
-- title:
--   Rat Ext: exists equiv
-- statement:
--   The Rat Ext construction uses the exists equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/RationalExtend.lean#L37-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/RationalExtend.lean#L37-L57

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
open ValuativeRel NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
variable {E R : Type} [Field E] [CommRing R] (ι : E →+* R)

theorem GlobalTheory.HL.RatExt.exists_equiv {n : ℕ} (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) :
    ∃ g' : (Fin n → R) ≃ₗ[R] (Fin n → R), ∀ x, g' (fun i => ι (x i)) = fun i => ι (g x i) := by sorry
