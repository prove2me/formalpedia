-- Prove2me | Theorems.Thm_GlobalTheory_nonempty_algHom_of_etale_of_isSepClosed
-- name    : GlobalTheory.nonempty_algHom_of_etale_of_isSepClosed
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:12:16.117362+00:00
-- url     : https://prove2.me/theorems/62ccd9da-95b0-4f3b-9bf9-0015e77f04c6
-- title:
--   Global Theory: nonempty alg Hom of etale of is Sep Closed
-- statement:
--   The Global Theory construction uses the nonempty alg Hom of etale of is Sep Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa.lean#L124-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa.lean#L124-L136

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial IsLocalRing
open scoped TensorProduct
variable {R A B K : Type*} [CommRing R] [CommRing A] [CommRing B] [Field K]
  [Algebra R A] [Algebra R B] [Algebra R K]

theorem GlobalTheory.nonempty_algHom_of_etale_of_isSepClosed [IsSepClosed K] [Algebra.Etale R A] (q : Ideal A)
    [q.IsPrime] (hq : q.comap (algebraMap R A) = RingHom.ker (algebraMap R K)) :
    Nonempty (A →ₐ[R] K) := by sorry
