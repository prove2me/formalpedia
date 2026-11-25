-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_Laurent_single_zero_one_cmul
-- name    : GroundTheory.PAdicHodge.Laurent.single_zero_one_cmul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:01:15.021269+00:00
-- url     : https://prove2.me/theorems/24258845-6d2f-4eda-925f-9c65bca59062
-- title:
--   Laurent: single zero one cmul
-- statement:
--   The Laurent construction uses the single zero one cmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L156-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L156-L157

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

theorem GroundTheory.PAdicHodge.Laurent.single_zero_one_cmul (a : ℤ → K) : cmul (Pi.single 0 1) a = a := by sorry
