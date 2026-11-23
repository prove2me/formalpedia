-- Prove2me | Theorems.Thm_GlobalTheory_degree_idealHilbertPoly_anti
-- name    : GlobalTheory.degree_idealHilbertPoly_anti
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:11:27.625341+00:00
-- url     : https://prove2.me/theorems/67fafce2-3437-4724-8081-4bbae6837b41
-- title:
--   Global Theory: degree ideal Hilbert Poly anti
-- statement:
--   The Global Theory construction uses the degree ideal Hilbert Poly anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RingKrullDimQuotientAddOneOfMemMinimalPrimesSup.lean#L154-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RingKrullDimQuotientAddOneOfMemMinimalPrimesSup.lean#L154-L166

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

theorem GlobalTheory.degree_idealHilbertPoly_anti {I J : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k))
    (hJ : J.IsHomogeneous (homogeneousSubmodule ι k)) (h : I ≤ J) :
    (idealHilbertPoly J).degree ≤ (idealHilbertPoly I).degree := by sorry
