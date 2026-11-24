-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_Laurent_weight_lt_of_highIndex_lt
-- name    : GroundTheory.PAdicHodge.Laurent.weight_lt_of_highIndex_lt
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:49:20.916683+00:00
-- url     : https://prove2.me/theorems/7b3bc658-ce63-422e-a7a6-f9e7c972342a
-- title:
--   Laurent: weight lt of high Index lt
-- statement:
--   The Laurent construction uses the weight lt of high Index lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L310-L312
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L310-L312

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

theorem GroundTheory.PAdicHodge.Laurent.weight_lt_of_highIndex_lt {n : ℤ} (hn : highIndex a ρ < n) :
    ‖a n‖ * ρ ^ n < gaussNorm a ρ := by sorry
