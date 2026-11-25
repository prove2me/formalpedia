-- Prove2me | Theorems.Thm_GlobalTheory_CommonDenominator_algebraMap_mem_O
-- name    : GlobalTheory.CommonDenominator.algebraMap_mem_O
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:17:38.166458+00:00
-- url     : https://prove2.me/theorems/68d07324-77d0-410c-a13a-52b7b1fa0739
-- title:
--   Common Denominator: algebra Map mem O
-- statement:
--   The Common Denominator construction uses the algebra Map mem O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/AlgebraMapMemO.lean#L11-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/AlgebraMapMemO.lean#L11-L17

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

theorem GlobalTheory.CommonDenominator.algebraMap_mem_O (L : Formalism.MainNotions.S.Loc.LocE F E) (t : 𝒪[F]) :
    algebraMap F E (t : F) ∈ L.O := by sorry
