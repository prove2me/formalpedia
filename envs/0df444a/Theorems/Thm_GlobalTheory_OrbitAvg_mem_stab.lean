-- Prove2me | Theorems.Thm_GlobalTheory_OrbitAvg_mem_stab
-- name    : GlobalTheory.OrbitAvg.mem_stab
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:32:21.680496+00:00
-- url     : https://prove2.me/theorems/e2e330de-4b78-4f50-8b25-613f0a997897
-- title:
--   Orbit Avg: mem stab
-- statement:
--   The Orbit Avg construction uses the mem stab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAveragingProjection.lean#L21-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAveragingProjection.lean#L21-L21

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

theorem GlobalTheory.OrbitAvg.mem_stab {x : V} {l : L} : l ∈ stab π L x ↔ π (l : G) x = x := by sorry
