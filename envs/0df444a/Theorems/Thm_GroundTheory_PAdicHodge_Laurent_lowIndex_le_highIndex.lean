-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_Laurent_lowIndex_le_highIndex
-- name    : GroundTheory.PAdicHodge.Laurent.lowIndex_le_highIndex
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:01:13.180421+00:00
-- url     : https://prove2.me/theorems/e42e0897-3e2d-5d1f-a732-aefd7ff0495f
-- title:
--   Laurent: low Index le high Index
-- statement:
--   The Laurent construction uses the low Index le high Index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L303-L304
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L303-L304

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

theorem GroundTheory.PAdicHodge.Laurent.lowIndex_le_highIndex : lowIndex a ρ ≤ highIndex a ρ := by sorry
