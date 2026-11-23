-- Prove2me | Theorems.Thm_GlobalTheory_exists_isSymm_map_eq
-- name    : GlobalTheory.exists_isSymm_map_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:21:51.275062+00:00
-- url     : https://prove2.me/theorems/76bd5a56-1dd9-4922-82c3-97bcefa71e66
-- title:
--   Global Theory: exists is Symm map eq
-- statement:
--   The Global Theory construction uses the exists is Symm map eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsSymplecticBasisToMatrixOffDiagDvd.lean#L204-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsSymplecticBasisToMatrixOffDiagDvd.lean#L204-L207

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
omit [Fintype l] [DecidableEq l]

theorem GlobalTheory.exists_isSymm_map_eq (hf : Surjective f) {X : Matrix l l R} (hX : X.IsSymm) :
    ∃ Y : Matrix l l S, Y.IsSymm ∧ Y.map f = X := by sorry
