-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_Laurent_le_of_mem_domSet
-- name    : GroundTheory.PAdicHodge.Laurent.le_of_mem_domSet
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:45:29.220646+00:00
-- url     : https://prove2.me/theorems/a2e12adb-4a82-41d8-8c5c-a95f7bbc6680
-- title:
--   Laurent: le of mem dom Set
-- statement:
--   The Laurent construction uses the le of mem dom Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L459-L481
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L459-L481

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
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
open GroundTheory GroundTheory.PAdicHodge
open Filter Topology
open GroundTheory.PAdicHodge.Laurent
set_option linter.unusedSectionVars false
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {a b c : ℤ → K} {ρ : ℝ}

theorem GroundTheory.PAdicHodge.Laurent.le_of_mem_domSet {ρ' : ℝ} (hρ : 0 < ρ) (hρρ' : ρ < ρ') (h : ConvergesAt a ρ)
    (h' : ConvergesAt a ρ') (ha : a ≠ 0) {n m : ℤ} (hn : n ∈ domSet a ρ)
    (hm : m ∈ domSet a ρ') : n ≤ m := by sorry
