-- Prove2me | Theorems.Thm_GlobalTheory_injective_of_finite_of_ringKrullDim_eq
-- name    : GlobalTheory.injective_of_finite_of_ringKrullDim_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:55:31.357903+00:00
-- url     : https://prove2.me/theorems/2e62b328-852f-48d4-8667-eea14dd2861f
-- title:
--   Global Theory: injective of finite of ring Krull Dim eq
-- statement:
--   The Global Theory construction uses the injective of finite of ring Krull Dim eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRingKrullDimQuotientMvPolynomialEqNat.lean#L281-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRingKrullDimQuotientMvPolynomialEqNat.lean#L281-L299

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

theorem GlobalTheory.injective_of_finite_of_ringKrullDim_eq {k S : Type*} [Field k] [CommRing S] {δ : ℕ}
    (φ : MvPolynomial (Fin δ) k →+* S) (hφ : φ.Finite) (hdim : ringKrullDim S = δ) :
    Function.Injective φ := by sorry
