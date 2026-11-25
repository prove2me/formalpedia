-- Prove2me | Theorems.Thm_GlobalTheory_addVal_discr_eq_two_mul_length_add_of_equiv
-- name    : GlobalTheory.addVal_discr_eq_two_mul_length_add_of_equiv
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:17:55.412252+00:00
-- url     : https://prove2.me/theorems/bd37e56e-9539-4e92-a1d2-385c4d1182bc
-- title:
--   Global Theory: add Val discr eq two mul length add of equiv
-- statement:
--   The Global Theory construction uses the add Val discr eq two mul length add of equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean#L58-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean#L58-L66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableSpanSpanOfDetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDiscreteValuationRing Polynomial
open scoped TensorProduct
open GlobalTheory
variable {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S] [Fintype ι] [DecidableEq ι]
variable [IsDomain R] [IsDiscreteValuationRing R]

theorem GlobalTheory.addVal_discr_eq_two_mul_length_add_of_equiv {M : Type*} [AddCommGroup M] [Module R M]
    (φ : M ≃ₗ[R] S) (e : Basis ι R S) (v : ι → M) :
    addVal R (Algebra.discr R fun i => φ (v i)) =
      2 * Module.length R (M ⧸ Submodule.span R (Set.range v)) + addVal R (Algebra.discr R e) := by sorry
