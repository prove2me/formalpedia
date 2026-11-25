-- Prove2me | Theorems.Thm_GlobalTheory_HL_sum_eq_sum_of_symm_rel
-- name    : GlobalTheory.HL.sum_eq_sum_of_symm_rel
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:39:59.821954+00:00
-- url     : https://prove2.me/theorems/258b33ad-5b65-504b-9619-302237fb11a8
-- title:
--   HL: sum eq sum of symm rel
-- statement:
--   The HL construction uses the sum eq sum of symm rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormOrbitSumLeOfSymmKernel.lean#L10-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormOrbitSumLeOfSymmKernel.lean#L10-L28

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolMulPosLeConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormOrbitSumLeOfSymmKernel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL

theorem GlobalTheory.HL.sum_eq_sum_of_symm_rel {ι : Type*} (Z : Finset ι) (r : ι → ι → Prop)
    (hr : ∀ p q, r p q → r q p) (hne : ∀ p ∈ Z, ∃ q ∈ Z, r p q) (F H : ι → ℂ)
    (hFH : ∀ p ∈ Z, ∀ q ∈ Z, r p q →
      F p * ((Z.filter (r q)).card : ℂ) = H q * ((Z.filter (r p)).card : ℂ)) :
    ∑ p ∈ Z, F p = ∑ p ∈ Z, H p := by sorry
