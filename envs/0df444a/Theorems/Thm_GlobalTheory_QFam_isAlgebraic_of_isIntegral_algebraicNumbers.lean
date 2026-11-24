-- Prove2me | Theorems.Thm_GlobalTheory_QFam_isAlgebraic_of_isIntegral_algebraicNumbers
-- name    : GlobalTheory.QFam.isAlgebraic_of_isIntegral_algebraicNumbers
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:01:35.443535+00:00
-- url     : https://prove2.me/theorems/1748df7c-2848-4538-8f6f-7780ac11c9b0
-- title:
--   QFam: is Algebraic of is Integral algebraic Numbers
-- statement:
--   The QFam construction uses the is Algebraic of is Integral algebraic Numbers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAlgebraicOfIsIntegralAlgebraicNumbers.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAlgebraicOfIsIntegralAlgebraicNumbers.lean#L14-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQPrin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModJTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralModularFamilyValueDivPeriodPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAlgebraicOfIsIntegralAlgebraicNumbers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory GlobalTheory.QFam

theorem GlobalTheory.QFam.isAlgebraic_of_isIntegral_algebraicNumbers {x : ℂ}
    (hx : IsIntegral (integralClosure ℚ ℂ).toSubring x) : IsAlgebraic ℚ x := by sorry
