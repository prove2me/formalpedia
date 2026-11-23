-- Prove2me | Theorems.Thm_GlobalTheory_idealHilbertPoly_eq_sup_add_colon
-- name    : GlobalTheory.idealHilbertPoly_eq_sup_add_colon
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:11:26.034161+00:00
-- url     : https://prove2.me/theorems/fa2978ab-7c7a-457b-b608-c05b34c6a4a3
-- title:
--   Global Theory: ideal Hilbert Poly eq sup add colon
-- statement:
--   The Global Theory construction uses the ideal Hilbert Poly eq sup add colon property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RingKrullDimQuotientAddOneOfMemMinimalPrimesSup.lean#L125-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RingKrullDimQuotientAddOneOfMemMinimalPrimesSup.lean#L125-L139

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

theorem GlobalTheory.idealHilbertPoly_eq_sup_add_colon {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) {f : MvPolynomial ι k} {d : ℕ}
    (hf : f.IsHomogeneous d) :
    idealHilbertPoly I = idealHilbertPoly (I ⊔ Ideal.span {f}) +
      (idealHilbertPoly (Submodule.colon I {f})).comp (Polynomial.X - Polynomial.C (d : ℚ)) := by sorry
