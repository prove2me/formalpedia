-- Prove2me | Theorems.Thm_GlobalTheory_finite_aeval_of_smul_mem_formCombinations
-- name    : GlobalTheory.finite_aeval_of_smul_mem_formCombinations
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:46:36.829304+00:00
-- url     : https://prove2.me/theorems/e29c5908-741b-473d-b0f7-529b69304e7b
-- title:
--   Global Theory: finite aeval of smul mem form Combinations
-- statement:
--   The Global Theory construction uses the finite aeval of smul mem form Combinations property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsFormsAlgebraicIndependentSmulSubSumMem.lean#L132-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsFormsAlgebraicIndependentSmulSubSumMem.lean#L132-L154

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
variable {σ ι R : Type*} [CommRing R]
variable [Fintype ι]

theorem GlobalTheory.finite_aeval_of_smul_mem_formCombinations [Finite σ] {I : Ideal (MvPolynomial σ R)}
    {F : ι → MvPolynomial σ R} {a : R} {e d₀ : ℕ} (he : 0 < e) (hed : e ≤ d₀)
    (h : ∀ d, d₀ ≤ d → ∀ p : MvPolynomial σ R, p.IsHomogeneous d →
      a • p ∈ formCombinations I F (d - e))
    {R' S' : Type*} [CommRing R'] [CommRing S'] [Algebra R R'] [Algebra R' S']
    (ha : IsUnit (algebraMap R R' a)) (π' : MvPolynomial σ R' →ₐ[R'] S')
    (hπ' : Function.Surjective π') (hI : ∀ p ∈ I, π' (map (algebraMap R R') p) = 0) :
    (aeval (fun i => π' (map (algebraMap R R') (F i))) : MvPolynomial ι R' →ₐ[R'] S').Finite := by sorry
