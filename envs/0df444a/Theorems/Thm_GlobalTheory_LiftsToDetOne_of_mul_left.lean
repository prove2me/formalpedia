-- Prove2me | Theorems.Thm_GlobalTheory_LiftsToDetOne_of_mul_left
-- name    : GlobalTheory.LiftsToDetOne.of_mul_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:20:47.867203+00:00
-- url     : https://prove2.me/theorems/9afdc9a5-b706-40ca-a2c2-20ded8261c81
-- title:
--   Lifts To Det One: of mul left
-- statement:
--   The Lifts To Det One construction uses the of mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsSymplecticBasisToMatrixOffDiagDvd.lean#L62-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsSymplecticBasisToMatrixOffDiagDvd.lean#L62-L65

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

theorem GlobalTheory.LiftsToDetOne.of_mul_left {E A : Matrix n n R} (hE : LiftsToDetOne f E) (h : LiftsToDetOne f (E * A)) :
    LiftsToDetOne f A := by sorry
