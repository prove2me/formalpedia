-- Prove2me | Theorems.Thm_GlobalTheory_ReducedAlg_isReduced_tensor_of_forall_prime
-- name    : GlobalTheory.ReducedAlg.isReduced_tensor_of_forall_prime
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:59:30.182095+00:00
-- url     : https://prove2.me/theorems/985206e9-55e2-4e9d-9839-63bf9f06a549
-- title:
--   Reduced Alg: is Reduced tensor of forall prime
-- statement:
--   The Reduced Alg construction uses the is Reduced tensor of forall prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/EqZeroOfForallLTensorEqZero.lean#L32-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/EqZeroOfForallLTensorEqZero.lean#L32-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_EqZeroOfForallLTensorEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.ReducedAlg

theorem GlobalTheory.ReducedAlg.isReduced_tensor_of_forall_prime {k : Type*} [Field k] (C A : Type*) [CommRing C]
    [Algebra k C] [CommRing A] [Algebra k A] [IsReduced A]
    (h : ∀ (p : Ideal A) [p.IsPrime], IsReduced (C ⊗[k] (A ⧸ p))) : IsReduced (C ⊗[k] A) := by sorry
