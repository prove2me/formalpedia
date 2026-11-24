-- Prove2me | Theorems.Thm_GlobalTheory_liftsToDetOne_of_isUnit_corner
-- name    : GlobalTheory.liftsToDetOne_of_isUnit_corner
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:07:18.245589+00:00
-- url     : https://prove2.me/theorems/ca0b400d-3606-407c-ba89-2a5a71b49648
-- title:
--   Global Theory: lifts To Det One of is Unit corner
-- statement:
--   The Global Theory construction uses the lifts To Det One of is Unit corner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsSymplecticBasisToMatrixOffDiagDvd.lean#L143-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsSymplecticBasisToMatrixOffDiagDvd.lean#L143-L160

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

theorem GlobalTheory.liftsToDetOne_of_isUnit_corner (hf : Surjective f)
    (ih : ∀ D : Matrix m m R, D.det = 1 → LiftsToDetOne f D)
    {A : Matrix (Unit ⊕ m) (Unit ⊕ m) R} (hA : A.det = 1)
    (h1 : IsUnit (A (.inl ()) (.inl ()))) : LiftsToDetOne f A := by sorry
