-- Prove2me | Theorems.Thm_GlobalTheory_SgLoc_isIntegral_valInteger_iff
-- name    : GlobalTheory.SgLoc.isIntegral_valInteger_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:47:54.471471+00:00
-- url     : https://prove2.me/theorems/cc2af5d0-427a-547a-84e1-a2c33f54027d
-- title:
--   Sg Loc: is Integral val Integer iff
-- statement:
--   The Sg Loc construction uses the is Integral val Integer iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsIntegralValIntegerIff.lean#L86-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsIntegralValIntegerIff.lean#L86-L89

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RowRawRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralValIntegerIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel MeasureTheory ComplexConjugate Formalism.MainNotions.S.Loc GlobalTheory.SgLoc
open scoped ComplexOrder
open GlobalTheory GlobalTheory.SgLoc

theorem GlobalTheory.SgLoc.isIntegral_valInteger_iff {F : Type} [Field F] [ValuativeRel F] (a : F) :
    IsIntegral 𝒪[F] a ↔ a ∈ 𝒪[F] := by sorry
