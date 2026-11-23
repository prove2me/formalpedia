-- Prove2me | Theorems.Thm_GlobalTheory_idealHilbertPoly_ne_zero_of_X_notMem
-- name    : GlobalTheory.idealHilbertPoly_ne_zero_of_X_notMem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:20.739827+00:00
-- url     : https://prove2.me/theorems/5a84863e-c695-4d3f-9859-8fb9d48b4f49
-- title:
--   Global Theory: ideal Hilbert Poly ne zero of X not Mem
-- statement:
--   The Global Theory construction uses the ideal Hilbert Poly ne zero of X not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RingKrullDimQuotientAddOneOfMemMinimalPrimesSup.lean#L184-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RingKrullDimQuotientAddOneOfMemMinimalPrimesSup.lean#L184-L195

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

theorem GlobalTheory.idealHilbertPoly_ne_zero_of_X_notMem {P : Ideal (MvPolynomial ι k)} [hP : P.IsPrime]
    (hI : P.IsHomogeneous (homogeneousSubmodule ι k)) {i : ι}
    (h : (X i : MvPolynomial ι k) ∉ P) : idealHilbertPoly P ≠ 0 := by sorry
