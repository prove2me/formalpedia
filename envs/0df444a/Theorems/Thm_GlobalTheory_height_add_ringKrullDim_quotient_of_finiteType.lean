-- Prove2me | Theorems.Thm_GlobalTheory_height_add_ringKrullDim_quotient_of_finiteType
-- name    : GlobalTheory.height_add_ringKrullDim_quotient_of_finiteType
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:56:37.118036+00:00
-- url     : https://prove2.me/theorems/9025525b-7572-4b18-aa60-858ffa902cb0
-- title:
--   Global Theory: height add ring Krull Dim quotient of finite Type
-- statement:
--   The Global Theory construction uses the height add ring Krull Dim quotient of finite Type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RingKrullDimQuotientAddOneOfMemMinimalPrimesSup.lean#L12-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RingKrullDimQuotientAddOneOfMemMinimalPrimesSup.lean#L12-L43

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

theorem GlobalTheory.height_add_ringKrullDim_quotient_of_finiteType (k : Type*) {A : Type*} [Field k]
    [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] (q : Ideal A) [q.IsPrime] :
    (q.height : WithBot ℕ∞) + ringKrullDim (A ⧸ q) = ringKrullDim A := by sorry
