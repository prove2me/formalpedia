-- Prove2me | Theorems.Thm_GlobalTheory_nonempty_quotient_map_algebraMap_ringEquiv
-- name    : GlobalTheory.nonempty_quotient_map_algebraMap_ringEquiv
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:12:29.404226+00:00
-- url     : https://prove2.me/theorems/c6b2c34f-45c7-49ce-a6fb-d1d01871e855
-- title:
--   Global Theory: nonempty quotient map algebra Map ring Equiv
-- statement:
--   The Global Theory construction uses the nonempty quotient map algebra Map ring Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsFormsAlgebraicIndependentSmulSubSumMem.lean#L217-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsFormsAlgebraicIndependentSmulSubSumMem.lean#L217-L231

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormsAlgebraicIndependentSmulSubSumMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {σ : Type*} {o : Type*} [CommRing o]

theorem GlobalTheory.nonempty_quotient_map_algebraMap_ringEquiv (I : Ideal (MvPolynomial σ o)) (J : Ideal o) :
    Nonempty (((MvPolynomial σ o ⧸ I) ⧸ J.map (algebraMap o (MvPolynomial σ o ⧸ I))) ≃+*
      (MvPolynomial σ (o ⧸ J) ⧸ I.map (map (Ideal.Quotient.mk J)))) := by sorry
