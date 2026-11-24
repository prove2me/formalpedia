-- Prove2me | Theorems.Thm_GlobalTheory_cast_hilbertDegree_of_degree_eq
-- name    : GlobalTheory.cast_hilbertDegree_of_degree_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:07:45.892987+00:00
-- url     : https://prove2.me/theorems/5641a988-0dbb-491d-a1e7-1e71d8b5fef1
-- title:
--   Global Theory: cast hilbert Degree of degree eq
-- statement:
--   The Global Theory construction uses the cast hilbert Degree of degree eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LeadingCoeffNonnegOfEventuallyEvalNat.lean#L219-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LeadingCoeffNonnegOfEventuallyEvalNat.lean#L219-L223

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

theorem GlobalTheory.cast_hilbertDegree_of_degree_eq [Finite ι] {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) {e : ℕ}
    (he : (idealHilbertPoly I).degree = e) :
    (hilbertDegree I : ℚ) = (e.factorial : ℚ) * (idealHilbertPoly I).coeff e := by sorry
