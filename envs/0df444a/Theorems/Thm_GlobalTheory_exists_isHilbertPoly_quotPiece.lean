-- Prove2me | Theorems.Thm_GlobalTheory_exists_isHilbertPoly_quotPiece
-- name    : GlobalTheory.exists_isHilbertPoly_quotPiece
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:33:07.501863+00:00
-- url     : https://prove2.me/theorems/d6b30d9b-6f28-4187-8831-d9bf8f15b691
-- title:
--   Global Theory: exists is Hilbert Poly quot Piece
-- statement:
--   The Global Theory construction uses the exists is Hilbert Poly quot Piece property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LeadingCoeffNonnegOfEventuallyEvalNat.lean#L128-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LeadingCoeffNonnegOfEventuallyEvalNat.lean#L128-L153

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

theorem GlobalTheory.exists_isHilbertPoly_quotPiece [Fintype ι] {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) :
    ∃ P : ℚ[X], IsHilbertPoly (quotPiece I) P ∧ P.degree < (Fintype.card ι : ℕ) := by sorry
