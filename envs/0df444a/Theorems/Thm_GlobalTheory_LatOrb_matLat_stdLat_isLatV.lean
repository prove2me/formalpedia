-- Prove2me | Theorems.Thm_GlobalTheory_LatOrb_matLat_stdLat_isLatV
-- name    : GlobalTheory.LatOrb.matLat_stdLat_isLatV
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:59:17.310877+00:00
-- url     : https://prove2.me/theorems/a3368232-49cb-4736-b7b6-480c6a2261b9
-- title:
--   Lat Orb: mat Lat std Lat is Lat V
-- statement:
--   The Lat Orb construction uses the mat Lat std Lat is Lat V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsFullRankLatticeImageStandardLatticeGL.lean#L39-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsFullRankLatticeImageStandardLatticeGL.lean#L39-L58

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
open GlobalTheory.LatOrbIsLat

theorem GlobalTheory.LatOrb.matLat_stdLat_isLatV : ∀ {O K : Type} [CommRing O] [Field K] [Algebra O K] (n : ℕ) (g : GL (Fin n) K),
    IsLatV O (matLat O g.val (stdLat O n)) := by sorry
