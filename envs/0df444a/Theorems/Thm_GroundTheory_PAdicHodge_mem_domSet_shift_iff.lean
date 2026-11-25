-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_mem_domSet_shift_iff
-- name    : GroundTheory.PAdicHodge.mem_domSet_shift_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:28:53.465849+00:00
-- url     : https://prove2.me/theorems/a560b4de-c012-4bf0-9ce1-8b103e9adbaf
-- title:
--   PAdic Hodge: mem dom Set shift iff
-- statement:
--   The PAdic Hodge construction uses the mem dom Set shift iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaBounded.lean#L468-L471
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaBounded.lean#L468-L471

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaBounded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.PAdicHodge
open Laurent Filter Topology
variable {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] {a : ℤ → L} {ρ : ℝ}

theorem GroundTheory.PAdicHodge.mem_domSet_shift_iff (hρ0 : 0 < ρ) (N k : ℤ) :
    k ∈ domSet (fun k => a (k + N)) ρ ↔ k + N ∈ domSet a ρ := by sorry
