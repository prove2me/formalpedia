-- Prove2me | Theorems.Thm_GlobalTheory_LiftsToSymplectic_upper
-- name    : GlobalTheory.LiftsToSymplectic.upper
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:12:06.086701+00:00
-- url     : https://prove2.me/theorems/fcd2d999-1058-4304-aeb5-a0a11a031891
-- title:
--   Lifts To Symplectic: upper
-- statement:
--   The Lifts To Symplectic construction uses the upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsSymplecticBasisToMatrixOffDiagDvd.lean#L220-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsSymplecticBasisToMatrixOffDiagDvd.lean#L220-L224

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
  {l : Type*} [Fintype l] [DecidableEq l]
open GlobalTheory.LiftsToSymplectic

theorem GlobalTheory.LiftsToSymplectic.upper (hf : Surjective f) {X : Matrix l l R} (hX : X.IsSymm) :
    LiftsToSymplectic f (fromBlocks 1 X 0 1) := by sorry
