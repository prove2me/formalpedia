-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_Laurent_cmul_single_zero_one
-- name    : GroundTheory.PAdicHodge.Laurent.cmul_single_zero_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:46:11.434711+00:00
-- url     : https://prove2.me/theorems/63f13a70-c410-4d5e-b39f-520e6886732f
-- title:
--   Laurent: cmul single zero one
-- statement:
--   The Laurent construction uses the cmul single zero one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L150-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L150-L154

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

theorem GroundTheory.PAdicHodge.Laurent.cmul_single_zero_one (a : ℤ → K) : cmul a (Pi.single 0 1) = a := by sorry
