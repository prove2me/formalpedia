-- Prove2me | Theorems.Thm_GlobalTheory_LiftsToDetOne_lower
-- name    : GlobalTheory.LiftsToDetOne.lower
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:12:49.440585+00:00
-- url     : https://prove2.me/theorems/27442123-f003-4e44-8dcf-eeebed6655fc
-- title:
--   Lifts To Det One: lower
-- statement:
--   The Lifts To Det One construction uses the lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsSymplecticBasisToMatrixOffDiagDvd.lean#L80-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsSymplecticBasisToMatrixOffDiagDvd.lean#L80-L84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Module Function
open private exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot from
  Mathlib.LinearAlgebra.SymplecticGroup
open GlobalTheory
variable {S R : Type*} [CommRing S] [CommRing R] {f : S →+* R}
  {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
open GlobalTheory.LiftsToDetOne

theorem GlobalTheory.LiftsToDetOne.lower (hf : Surjective f) (X : Matrix m n R) :
    LiftsToDetOne f (fromBlocks (1 : Matrix n n R) 0 X (1 : Matrix m m R)) := by sorry
