-- Prove2me | Theorems.Thm_GlobalTheory_LatOrb_matLat_mul
-- name    : GlobalTheory.LatOrb.matLat_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T15:51:08.584889+00:00
-- url     : https://prove2.me/theorems/6f1eecae-b56c-4f21-9b6a-76dbb6759dc5
-- title:
--   Lat Orb: mat Lat mul
-- statement:
--   The Lat Orb construction uses the mat Lat mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemMatLat.lean#L43-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemMatLat.lean#L43-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LatOrb
open Polynomial Matrix
variable (O : Type) {K : Type} [CommRing O] [Field K] [Algebra O K]
variable {O}

theorem GlobalTheory.LatOrb.matLat_mul {n : ℕ} (a b : Matrix (Fin n) (Fin n) K) (M : Submodule O (Fin n → K)) :
    matLat O (a * b) M = matLat O a (matLat O b M) := by sorry
