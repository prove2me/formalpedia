-- Prove2me | Theorems.Thm_GlobalTheory_LatOrb_mem_stdLat
-- name    : GlobalTheory.LatOrb.mem_stdLat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:20:38.169251+00:00
-- url     : https://prove2.me/theorems/2052ff2c-07d9-46db-a8a2-f7a5b9847dc7
-- title:
--   Lat Orb: mem std Lat
-- statement:
--   The Lat Orb construction uses the mem std Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemMatLat.lean#L36-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemMatLat.lean#L36-L37

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

theorem GlobalTheory.LatOrb.mem_stdLat {n : ℕ} (v : Fin n → K) : v ∈ stdLat O n ↔ ∀ i, v i ∈ (algebraMap O K).range := by sorry
