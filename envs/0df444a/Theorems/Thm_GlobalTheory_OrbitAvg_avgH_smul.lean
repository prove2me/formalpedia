-- Prove2me | Theorems.Thm_GlobalTheory_OrbitAvg_avgH_smul
-- name    : GlobalTheory.OrbitAvg.avgH_smul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:37:38.588567+00:00
-- url     : https://prove2.me/theorems/7bcb9916-3cb6-4cac-8c1f-ee6c66f86d95
-- title:
--   Orbit Avg: avg H smul
-- statement:
--   The Orbit Avg construction uses the avg H smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAveragingProjection.lean#L115-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAveragingProjection.lean#L115-L120

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAveragingProjection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.OrbitAvg
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
  (π : G →* Module.End ℂ V) (L : Subgroup G)

theorem GlobalTheory.OrbitAvg.avgH_smul (H : Subgroup L) [H.FiniteIndex] (c : ℂ) (x : V) :
    avgH π L H (c • x) = c • avgH π L H x := by sorry
