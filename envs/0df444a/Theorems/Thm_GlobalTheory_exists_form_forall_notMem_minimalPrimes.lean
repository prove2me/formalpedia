-- Prove2me | Theorems.Thm_GlobalTheory_exists_form_forall_notMem_minimalPrimes
-- name    : GlobalTheory.exists_form_forall_notMem_minimalPrimes
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:32:39.824352+00:00
-- url     : https://prove2.me/theorems/78581c37-2881-466f-a29e-cd6239ad971e
-- title:
--   Global Theory: exists form forall not Mem minimal Primes
-- statement:
--   The Global Theory construction uses the exists form forall not Mem minimal Primes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRingKrullDimQuotientMvPolynomialEqNat.lean#L121-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRingKrullDimQuotientMvPolynomialEqNat.lean#L121-L146

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
variable {σ : Type*}
variable [Finite σ] {k : Type*} [Field k]

theorem GlobalTheory.exists_form_forall_notMem_minimalPrimes {J : Ideal (MvPolynomial σ k)}
    (hJ : J.IsHomogeneous (homogeneousSubmodule σ k)) (h : ¬ idealOfVars σ k ≤ J.radical) :
    ∃ n, 0 < n ∧ ∃ f : MvPolynomial σ k, f.IsHomogeneous n ∧ ∀ p ∈ J.minimalPrimes, f ∉ p := by sorry
