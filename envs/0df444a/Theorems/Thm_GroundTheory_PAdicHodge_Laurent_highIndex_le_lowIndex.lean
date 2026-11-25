-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_Laurent_highIndex_le_lowIndex
-- name    : GroundTheory.PAdicHodge.Laurent.highIndex_le_lowIndex
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:01:00.711448+00:00
-- url     : https://prove2.me/theorems/a8457c84-60ba-5b65-afb6-4e72731b207f
-- title:
--   Laurent: high Index le low Index
-- statement:
--   The Laurent construction uses the high Index le low Index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L483-L486
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L483-L486

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

theorem GroundTheory.PAdicHodge.Laurent.highIndex_le_lowIndex {ρ' : ℝ} (hρ : 0 < ρ) (hρρ' : ρ < ρ') (h : ConvergesAt a ρ)
    (h' : ConvergesAt a ρ') (ha : a ≠ 0) : highIndex a ρ ≤ lowIndex a ρ' := by sorry
