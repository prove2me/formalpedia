-- Prove2me | Theorems.Thm_GlobalTheory_OrbitAvg_avg_eq
-- name    : GlobalTheory.OrbitAvg.avg_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:32:21.205264+00:00
-- url     : https://prove2.me/theorems/f95811ff-f7bf-4f0d-92c2-6d53b125ee9a
-- title:
--   Orbit Avg: avg eq
-- statement:
--   The Orbit Avg construction uses the avg eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAveragingProjection.lean#L124-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAveragingProjection.lean#L124-L125

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

theorem GlobalTheory.OrbitAvg.avg_eq {H : Subgroup L} {x : V} [H.FiniteIndex] (hH : H ≤ stab π L x) :
    avg π L x = avgH π L H x := by sorry
