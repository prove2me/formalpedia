-- Prove2me | Theorems.Thm_GlobalTheory_quotPiece_natCast
-- name    : GlobalTheory.quotPiece_natCast
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:05:06.355802+00:00
-- url     : https://prove2.me/theorems/a75b436c-c016-497d-b645-8a0e60ea313f
-- title:
--   Global Theory: quot Piece nat Cast
-- statement:
--   The Global Theory construction uses the quot Piece nat Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LeadingCoeffNonnegOfEventuallyEvalNat.lean#L101-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LeadingCoeffNonnegOfEventuallyEvalNat.lean#L101-L103

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

theorem GlobalTheory.quotPiece_natCast (I : Ideal (MvPolynomial ι k)) (n : ℕ) :
    quotPiece I n = (homogeneousSubmodule ι k n).map (Ideal.Quotient.mkₐ k I).toLinearMap := by sorry
