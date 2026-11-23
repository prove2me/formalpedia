-- Prove2me | Theorems.Thm_GlobalTheory_LatOrb_mem_matLat
-- name    : GlobalTheory.LatOrb.mem_matLat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:04:14.756029+00:00
-- url     : https://prove2.me/theorems/e6fddabc-2871-4ff4-bbc4-9d705146fb02
-- title:
--   Lat Orb: mem mat Lat
-- statement:
--   The Lat Orb construction uses the mem mat Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemMatLat.lean#L39-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemMatLat.lean#L39-L41

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

theorem GlobalTheory.LatOrb.mem_matLat {n : ℕ} (g : Matrix (Fin n) (Fin n) K) (M : Submodule O (Fin n → K))
    (v : Fin n → K) : v ∈ matLat O g M ↔ ∃ u ∈ M, g *ᵥ u = v := by sorry
