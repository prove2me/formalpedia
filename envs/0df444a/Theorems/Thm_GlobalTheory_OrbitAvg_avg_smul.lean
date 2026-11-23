-- Prove2me | Theorems.Thm_GlobalTheory_OrbitAvg_avg_smul
-- name    : GlobalTheory.OrbitAvg.avg_smul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:33:19.816493+00:00
-- url     : https://prove2.me/theorems/7f0c2674-c969-48ad-9c50-8262246bac5e
-- title:
--   Orbit Avg: avg smul
-- statement:
--   The Orbit Avg construction uses the avg smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAveragingProjection.lean#L169-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAveragingProjection.lean#L169-L172

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

theorem GlobalTheory.OrbitAvg.avg_smul {x : V} (hx : (stab π L x).FiniteIndex) (c : ℂ) :
    avg π L (c • x) = c • avg π L x := by sorry
