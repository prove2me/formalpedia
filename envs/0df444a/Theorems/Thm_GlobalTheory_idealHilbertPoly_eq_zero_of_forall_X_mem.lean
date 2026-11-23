-- Prove2me | Theorems.Thm_GlobalTheory_idealHilbertPoly_eq_zero_of_forall_X_mem
-- name    : GlobalTheory.idealHilbertPoly_eq_zero_of_forall_X_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:15.9876+00:00
-- url     : https://prove2.me/theorems/f61ffd1b-ca36-4665-b07a-f82227f0f718
-- title:
--   Global Theory: ideal Hilbert Poly eq zero of forall X mem
-- statement:
--   The Global Theory construction uses the ideal Hilbert Poly eq zero of forall X mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RingKrullDimQuotientAddOneOfMemMinimalPrimesSup.lean#L168-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RingKrullDimQuotientAddOneOfMemMinimalPrimesSup.lean#L168-L182

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
open MvPolynomial DirectSum
variable {ι k : Type*} [Field k]
variable [Finite ι]

theorem GlobalTheory.idealHilbertPoly_eq_zero_of_forall_X_mem {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k))
    (h : ∀ i, (X i : MvPolynomial ι k) ∈ I) : idealHilbertPoly I = 0 := by sorry
