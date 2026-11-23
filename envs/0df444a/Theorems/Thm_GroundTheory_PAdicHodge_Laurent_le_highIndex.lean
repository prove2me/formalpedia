-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_Laurent_le_highIndex
-- name    : GroundTheory.PAdicHodge.Laurent.le_highIndex
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:39.694697+00:00
-- url     : https://prove2.me/theorems/36320654-ba0d-4ce6-8ade-bd49908d8607
-- title:
--   Laurent: le high Index
-- statement:
--   The Laurent construction uses the le high Index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L300-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L300-L301

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

theorem GroundTheory.PAdicHodge.Laurent.le_highIndex {n : ℤ} (hn : n ∈ domSet a ρ) : n ≤ highIndex a ρ := by sorry
