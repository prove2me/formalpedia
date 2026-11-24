-- Prove2me | Theorems.Thm_GlobalTheory_algebraicIndependent_of_quotient
-- name    : GlobalTheory.algebraicIndependent_of_quotient
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:05:25.445845+00:00
-- url     : https://prove2.me/theorems/8578c2c5-a1f3-4697-a390-bcdd8c470141
-- title:
--   Global Theory: algebraic Independent of quotient
-- statement:
--   The Global Theory construction uses the algebraic Independent of quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsFormsAlgebraicIndependentSmulSubSumMem.lean#L188-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsFormsAlgebraicIndependentSmulSubSumMem.lean#L188-L209

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

theorem GlobalTheory.algebraicIndependent_of_quotient {ι o S T : Type*} [CommRing o] [IsDedekindDomain o]
    [CommRing S] [Algebra o S] [Module.IsTorsionFree o S] {J : Ideal o} (hJ : J ≠ ⊤)
    [CommRing T] [Algebra (o ⧸ J) T] (ψ : S →+* T)
    (hψ : ∀ r : o, ψ (algebraMap o S r) = algebraMap (o ⧸ J) T (Ideal.Quotient.mk J r))
    {f : ι → S} (hf : AlgebraicIndependent (o ⧸ J) (fun i => ψ (f i))) :
    AlgebraicIndependent o f := by sorry
