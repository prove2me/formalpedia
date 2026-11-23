-- Prove2me | Theorems.Thm_GlobalTheory_finrank_quotPiece_add
-- name    : GlobalTheory.finrank_quotPiece_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:05:26.802048+00:00
-- url     : https://prove2.me/theorems/e45723ac-8a10-4e9b-9291-0a1af202505e
-- title:
--   Global Theory: finrank quot Piece add
-- statement:
--   The Global Theory construction uses the finrank quot Piece add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LeadingCoeffNonnegOfEventuallyEvalNat.lean#L182-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LeadingCoeffNonnegOfEventuallyEvalNat.lean#L182-L191

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

theorem GlobalTheory.finrank_quotPiece_add [Finite ι] (I : Ideal (MvPolynomial ι k)) (n : ℕ) :
    finrank k (quotPiece I n) +
      finrank k (I.restrictScalars k ⊓ homogeneousSubmodule ι k n : Submodule k _) =
      finrank k (homogeneousSubmodule ι k n) := by sorry
