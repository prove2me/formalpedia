-- Prove2me | Theorems.Thm_GlobalTheory_OrbitAvg_avgH_mem
-- name    : GlobalTheory.OrbitAvg.avgH_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:37:21.855415+00:00
-- url     : https://prove2.me/theorems/ce47df39-cebe-4c7b-a15b-2b62165c526a
-- title:
--   Orbit Avg: avg H mem
-- statement:
--   The Orbit Avg construction uses the avg H mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAveragingProjection.lean#L127-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAveragingProjection.lean#L127-L133

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

theorem GlobalTheory.OrbitAvg.avgH_mem (D : Submodule ℂ V) (hD : ∀ l ∈ L, ∀ x ∈ D, π l x ∈ D) (H : Subgroup L)
    [H.FiniteIndex] {x : V} (hx : x ∈ D) : avgH π L H x ∈ D := by sorry
