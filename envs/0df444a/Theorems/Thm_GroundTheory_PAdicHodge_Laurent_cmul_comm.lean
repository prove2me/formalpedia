-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_Laurent_cmul_comm
-- name    : GroundTheory.PAdicHodge.Laurent.cmul_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:02.516804+00:00
-- url     : https://prove2.me/theorems/35411472-2d08-47f1-94b4-fb8237c0d86e
-- title:
--   Laurent: cmul comm
-- statement:
--   The Laurent construction uses the cmul comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L144-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L144-L148

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

theorem GroundTheory.PAdicHodge.Laurent.cmul_comm (a b : ℤ → K) : cmul a b = cmul b a := by sorry
