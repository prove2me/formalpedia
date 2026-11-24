-- Prove2me | Theorems.Thm_GlobalTheory_ringKrullDim_quotient_radical_sup_succ_le
-- name    : GlobalTheory.ringKrullDim_quotient_radical_sup_succ_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:18:50.833195+00:00
-- url     : https://prove2.me/theorems/d077476d-3313-4100-82da-631cb266e4b0
-- title:
--   Global Theory: ring Krull Dim quotient radical sup succ le
-- statement:
--   The Global Theory construction uses the ring Krull Dim quotient radical sup succ le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRingKrullDimQuotientMvPolynomialEqNat.lean#L74-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRingKrullDimQuotientMvPolynomialEqNat.lean#L74-L90

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
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

theorem GlobalTheory.ringKrullDim_quotient_radical_sup_succ_le {A : Type*} [CommRing A] (J : Ideal A) {f : A}
    (hf : ∀ p ∈ J.minimalPrimes, f ∉ p) :
    ringKrullDim (A ⧸ (J.radical ⊔ Ideal.span {f})) + 1 ≤ ringKrullDim (A ⧸ J) := by sorry
