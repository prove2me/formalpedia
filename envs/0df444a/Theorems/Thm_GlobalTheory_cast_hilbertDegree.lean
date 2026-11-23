-- Prove2me | Theorems.Thm_GlobalTheory_cast_hilbertDegree
-- name    : GlobalTheory.cast_hilbertDegree
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:06:18.808201+00:00
-- url     : https://prove2.me/theorems/5dcb40f3-6479-4d9d-a907-bc5dc23b5e23
-- title:
--   Global Theory: cast hilbert Degree
-- statement:
--   The Global Theory construction uses the cast hilbert Degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LeadingCoeffNonnegOfEventuallyEvalNat.lean#L203-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LeadingCoeffNonnegOfEventuallyEvalNat.lean#L203-L217

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingCoeffNonnegOfEventuallyEvalNat
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

theorem GlobalTheory.cast_hilbertDegree [Finite ι] {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) :
    (hilbertDegree I : ℚ) =
      ((idealHilbertPoly I).natDegree.factorial : ℚ) * (idealHilbertPoly I).leadingCoeff := by sorry
