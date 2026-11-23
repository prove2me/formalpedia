-- Prove2me | Theorems.Thm_GlobalTheory_LiftsToSymplectic_mul
-- name    : GlobalTheory.LiftsToSymplectic.mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:12:38.439241+00:00
-- url     : https://prove2.me/theorems/b0d84ff2-0e2b-49d8-87ea-aefe3e90d500
-- title:
--   Lifts To Symplectic: mul
-- statement:
--   The Lifts To Symplectic construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsSymplecticBasisToMatrixOffDiagDvd.lean#L211-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsSymplecticBasisToMatrixOffDiagDvd.lean#L211-L215

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

theorem GlobalTheory.LiftsToSymplectic.mul {A B : Matrix (l ⊕ l) (l ⊕ l) R} (hA : LiftsToSymplectic f A)
    (hB : LiftsToSymplectic f B) : LiftsToSymplectic f (A * B) := by sorry
