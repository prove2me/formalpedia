-- Prove2me | Theorems.Thm_GlobalTheory_exists_smul_mem_formCombinations
-- name    : GlobalTheory.exists_smul_mem_formCombinations
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:41:59.747283+00:00
-- url     : https://prove2.me/theorems/79fabe61-ac28-4b20-b677-e39cff396ab9
-- title:
--   Global Theory: exists smul mem form Combinations
-- statement:
--   The Global Theory construction uses the exists smul mem form Combinations property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsFormsAlgebraicIndependentSmulSubSumMem.lean#L92-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsFormsAlgebraicIndependentSmulSubSumMem.lean#L92-L130

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

theorem GlobalTheory.exists_smul_mem_formCombinations [Finite σ] {I : Ideal (MvPolynomial σ R)}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ R)) (J : Ideal R)
    {F : ι → MvPolynomial σ R} {e n : ℕ} (hF : ∀ i, (F i).IsHomogeneous e)
    (h : ∀ q : MvPolynomial σ (R ⧸ J), q.IsHomogeneous (e + n) →
      q ∈ formCombinations (I.map (map (Ideal.Quotient.mk J)))
        (fun i => map (Ideal.Quotient.mk J) (F i)) n) :
    ∃ a : R, a - 1 ∈ J ∧ ∀ p : MvPolynomial σ R, p.IsHomogeneous (e + n) →
      a • p ∈ formCombinations I F n := by sorry
