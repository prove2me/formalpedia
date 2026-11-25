-- Prove2me | Theorems.Thm_GlobalTheory_IsHilbertPoly_idealHilbertPoly_eq
-- name    : GlobalTheory.IsHilbertPoly.idealHilbertPoly_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:11:33.477171+00:00
-- url     : https://prove2.me/theorems/64076886-5308-45b1-817b-7ad996979a0e
-- title:
--   Is Hilbert Poly: ideal Hilbert Poly eq
-- statement:
--   The Is Hilbert Poly construction uses the ideal Hilbert Poly eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LeadingCoeffNonnegOfEventuallyEvalNat.lean#L169-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LeadingCoeffNonnegOfEventuallyEvalNat.lean#L169-L173

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

theorem GlobalTheory.IsHilbertPoly.idealHilbertPoly_eq {I : Ideal (MvPolynomial ι k)} {P : ℚ[X]}
    (hP : IsHilbertPoly (quotPiece I) P) : idealHilbertPoly I = P := by sorry
