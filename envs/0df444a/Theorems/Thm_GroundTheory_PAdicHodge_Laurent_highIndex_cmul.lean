-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_Laurent_highIndex_cmul
-- name    : GroundTheory.PAdicHodge.Laurent.highIndex_cmul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:00:58.851179+00:00
-- url     : https://prove2.me/theorems/fc068802-4891-5719-b718-64993a147631
-- title:
--   Laurent: high Index cmul
-- statement:
--   The Laurent construction uses the high Index cmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L445-L455
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L445-L455

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
variable [CompleteSpace K]
variable (hρ : 0 < ρ) (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
include hρ ha hb ha0 hb0

theorem GroundTheory.PAdicHodge.Laurent.highIndex_cmul : highIndex (cmul a b) ρ = highIndex a ρ + highIndex b ρ := by sorry
