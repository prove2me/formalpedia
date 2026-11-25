-- Prove2me | Theorems.Thm_GlobalTheory_CommonDenominator_exists_den
-- name    : GlobalTheory.CommonDenominator.exists_den
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:17:14.605218+00:00
-- url     : https://prove2.me/theorems/8119dbfc-6a01-5456-8794-c181fc73ddc8
-- title:
--   Common Denominator: exists den
-- statement:
--   The Common Denominator construction uses the exists den property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/AlgebraMapMemO.lean#L19-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/AlgebraMapMemO.lean#L19-L30

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AlgebraMapMemO
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel
open GlobalTheory GlobalTheory.CommonDenominator
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem GlobalTheory.CommonDenominator.exists_den (L : Formalism.MainNotions.S.Loc.LocE F E) (c : E) :
    ∃ t : 𝒪[F], t ≠ 0 ∧ algebraMap F E (t : F) * c ∈ L.O := by sorry
