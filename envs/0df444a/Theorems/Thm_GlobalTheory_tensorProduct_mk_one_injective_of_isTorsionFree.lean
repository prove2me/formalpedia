-- Prove2me | Theorems.Thm_GlobalTheory_tensorProduct_mk_one_injective_of_isTorsionFree
-- name    : GlobalTheory.tensorProduct_mk_one_injective_of_isTorsionFree
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:51:34.14116+00:00
-- url     : https://prove2.me/theorems/11d10fba-acc8-5f2b-801e-b5b4423f902f
-- title:
--   Global Theory: tensor Product mk one injective of is Torsion Free
-- statement:
--   The Global Theory construction uses the tensor Product mk one injective of is Torsion Free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RangeAlgebraMapEqIInfDiscreteValuationSubring.lean#L625-L640
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RangeAlgebraMapEqIInfDiscreteValuationSubring.lean#L625-L640

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
universe u v w
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
  (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
open TensorProduct

theorem GlobalTheory.tensorProduct_mk_one_injective_of_isTorsionFree {S : Type*} [CommRing S] [IsDomain S]
    (F : Type*) [Field F] [Algebra S F] [FaithfulSMul S F] (M : Type*) [AddCommGroup M]
    [Module S M] [Module.IsTorsionFree S M] :
    Function.Injective (TensorProduct.mk S F M 1) := by sorry
