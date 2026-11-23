-- Prove2me | Theorems.Thm_GlobalTheory_LatOrbIsLat_single_mem_stdLat
-- name    : GlobalTheory.LatOrbIsLat.single_mem_stdLat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:26:09.983925+00:00
-- url     : https://prove2.me/theorems/e0d118eb-3c4e-4ee2-92b5-2bd8f2a0bf84
-- title:
--   Lat Orb Is Lat: single mem std Lat
-- statement:
--   The Lat Orb Is Lat construction uses the single mem std Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsFullRankLatticeImageStandardLatticeGL.lean#L8-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsFullRankLatticeImageStandardLatticeGL.lean#L8-L14

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsFullRankLatticeImageStandardLatticeGL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix GlobalTheory.LatOrb
open GlobalTheory GlobalTheory.LatOrbIsLat

theorem GlobalTheory.LatOrbIsLat.single_mem_stdLat {O K : Type} [CommRing O] [Field K] [Algebra O K] (n : ℕ) (i : Fin n) :
    (Pi.single i (1 : K) : Fin n → K) ∈ stdLat O n := by sorry
