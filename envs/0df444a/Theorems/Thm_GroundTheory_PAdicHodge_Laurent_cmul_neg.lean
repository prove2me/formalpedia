-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_Laurent_cmul_neg
-- name    : GroundTheory.PAdicHodge.Laurent.cmul_neg
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:01:06.427798+00:00
-- url     : https://prove2.me/theorems/c17905f4-fe50-51bb-b6a0-babf3ff751f1
-- title:
--   Laurent: cmul neg
-- statement:
--   The Laurent construction uses the cmul neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L184-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L184-L186

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

theorem GroundTheory.PAdicHodge.Laurent.cmul_neg (a b : ℤ → K) : cmul a (-b) = -cmul a b := by sorry
