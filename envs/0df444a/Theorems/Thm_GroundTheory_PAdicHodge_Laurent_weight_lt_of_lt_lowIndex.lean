-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_Laurent_weight_lt_of_lt_lowIndex
-- name    : GroundTheory.PAdicHodge.Laurent.weight_lt_of_lt_lowIndex
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:34:41.076686+00:00
-- url     : https://prove2.me/theorems/abe2eeb6-a858-493f-aeb2-5810e8756908
-- title:
--   Laurent: weight lt of lt low Index
-- statement:
--   The Laurent construction uses the weight lt of lt low Index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L306-L308
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L306-L308

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
variable (hρ : 0 < ρ) (h : ConvergesAt a ρ) (ha : a ≠ 0)
include hρ h ha

theorem GroundTheory.PAdicHodge.Laurent.weight_lt_of_lt_lowIndex {n : ℤ} (hn : n < lowIndex a ρ) :
    ‖a n‖ * ρ ^ n < gaussNorm a ρ := by sorry
