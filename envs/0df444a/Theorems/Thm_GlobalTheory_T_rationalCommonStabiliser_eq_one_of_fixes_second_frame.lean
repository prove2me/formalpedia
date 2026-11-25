-- Prove2me | Theorems.Thm_GlobalTheory_T_rationalCommonStabiliser_eq_one_of_fixes_second_frame
-- name    : GlobalTheory.T.rationalCommonStabiliser_eq_one_of_fixes_second_frame
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:59:46.399322+00:00
-- url     : https://prove2.me/theorems/e049197d-d527-468d-9490-1b5fb6ffbab2
-- title:
--   T: rational Common Stabiliser eq one of fixes second frame
-- statement:
--   The T construction uses the rational Common Stabiliser eq one of fixes second frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/RationalCommonStabiliserEqOneOfFixesSecondFrameStatement.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/RationalCommonStabiliserEqOneOfFixesSecondFrameStatement.lean#L12-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalCommonStabiliserEqOneOfFixesSecondFrame
import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalCommonStabiliserEqOneOfFixesSecondFrameStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.rationalCommonStabiliser_eq_one_of_fixes_second_frame : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ x ∈ G.St, (∀ b, x (G.f' b) = G.f' b) → x = 1 := by sorry
