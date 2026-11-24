-- Prove2me | Theorems.Thm_GlobalTheory_isBaseChange_fixedSubalgebra_tensor
-- name    : GlobalTheory.isBaseChange_fixedSubalgebra_tensor
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:55:55.325633+00:00
-- url     : https://prove2.me/theorems/7892414b-d0dc-4587-8805-cb599fed55b8
-- title:
--   Global Theory: is Base Change fixed Subalgebra tensor
-- statement:
--   The Global Theory construction uses the is Base Change fixed Subalgebra tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L376-L388
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L376-L388

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Pointwise
open GlobalTheory
variable (G : Type*) [Group G]
variable (R S A : Type*) [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]
  [MulSemiringAction G A] [SMulCommClass G R A]

theorem GlobalTheory.isBaseChange_fixedSubalgebra_tensor [Finite G] [Module.Flat R S] :
    letI := tensorMulSemiringAction G R S A
    haveI := tensorMulSemiringAction_smulCommClass G R S A
    IsBaseChange S (fixedSubalgebraMap G S
      (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A) (tensorMulSemiringAction_includeRight G R S A)).toLinearMap := by sorry
