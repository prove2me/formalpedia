-- Prove2me | Theorems.Thm_GlobalTheory_OrbitAvg_avg_fixed
-- name    : GlobalTheory.OrbitAvg.avg_fixed
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:33:11.890673+00:00
-- url     : https://prove2.me/theorems/a144c6f2-3461-4247-9a95-194a7898d371
-- title:
--   Orbit Avg: avg fixed
-- statement:
--   The Orbit Avg construction uses the avg fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAveragingProjection.lean#L135-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAveragingProjection.lean#L135-L144

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

theorem GlobalTheory.OrbitAvg.avg_fixed {x : V} (hx : (stab π L x).FiniteIndex) (hfix : ∀ l ∈ L, π l x = x) :
    avg π L x = x := by sorry
