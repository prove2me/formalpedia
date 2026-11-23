-- Prove2me | Theorems.Thm_GlobalTheory_ringKrullDim_quotient_add_one_of_mem_minimalPrimes_sup
-- name    : GlobalTheory.ringKrullDim_quotient_add_one_of_mem_minimalPrimes_sup
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:15:17.526655+00:00
-- url     : https://prove2.me/theorems/4f7f9761-7317-4e33-8a97-ec6756762a33
-- title:
--   Global Theory: ring Krull Dim quotient add one of mem minimal Primes sup
-- statement:
--   The Global Theory construction uses the ring Krull Dim quotient add one of mem minimal Primes sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RingKrullDimQuotientAddOneOfMemMinimalPrimesSup.lean#L45-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RingKrullDimQuotientAddOneOfMemMinimalPrimesSup.lean#L45-L67

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingCoeffNonnegOfEventuallyEvalNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RingKrullDimQuotientAddOneOfMemMinimalPrimesSup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter Module
open GlobalTheory
attribute [local instance] MvPolynomial.gradedAlgebra

theorem GlobalTheory.ringKrullDim_quotient_add_one_of_mem_minimalPrimes_sup (k : Type*) {A : Type*} [Field k]
    [CommRing A] [Algebra k A] [Algebra.FiniteType k A] {P Q : Ideal A} [P.IsPrime] {f : A}
    (hf : f ∉ P) (hQ : Q ∈ (P ⊔ Ideal.span {f}).minimalPrimes) :
    ringKrullDim (A ⧸ Q) + 1 = ringKrullDim (A ⧸ P) := by sorry
