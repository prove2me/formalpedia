-- Prove2me | Theorems.Thm_GlobalTheory_isHilbertPoly_idealHilbertPoly
-- name    : GlobalTheory.isHilbertPoly_idealHilbertPoly
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:05:49.142456+00:00
-- url     : https://prove2.me/theorems/733316a3-c64b-400f-a86b-57d6d0078cd1
-- title:
--   Global Theory: is Hilbert Poly ideal Hilbert Poly
-- statement:
--   The Global Theory construction uses the is Hilbert Poly ideal Hilbert Poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LeadingCoeffNonnegOfEventuallyEvalNat.lean#L160-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LeadingCoeffNonnegOfEventuallyEvalNat.lean#L160-L167

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

theorem GlobalTheory.isHilbertPoly_idealHilbertPoly [Finite ι] {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) :
    IsHilbertPoly (quotPiece I) (idealHilbertPoly I) := by sorry
