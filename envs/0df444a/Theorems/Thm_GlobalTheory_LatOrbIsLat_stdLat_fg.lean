-- Prove2me | Theorems.Thm_GlobalTheory_LatOrbIsLat_stdLat_fg
-- name    : GlobalTheory.LatOrbIsLat.stdLat_fg
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:58:51.761866+00:00
-- url     : https://prove2.me/theorems/eec5f44c-e824-4297-8f83-e592518fd959
-- title:
--   Lat Orb Is Lat: std Lat fg
-- statement:
--   The Lat Orb Is Lat construction uses the std Lat fg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsFullRankLatticeImageStandardLatticeGL.lean#L31-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsFullRankLatticeImageStandardLatticeGL.lean#L31-L34

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

theorem GlobalTheory.LatOrbIsLat.stdLat_fg {O K : Type} [CommRing O] [Field K] [Algebra O K] (n : ℕ) :
    (stdLat O n : Submodule O (Fin n → K)).FG := by sorry
