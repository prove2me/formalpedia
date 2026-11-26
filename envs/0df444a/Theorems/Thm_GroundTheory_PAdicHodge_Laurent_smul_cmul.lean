-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_Laurent_smul_cmul
-- name    : GroundTheory.PAdicHodge.Laurent.smul_cmul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:01:14.957137+00:00
-- url     : https://prove2.me/theorems/b1ce6114-fec1-4061-94a7-3580bc10b0db
-- title:
--   Laurent: smul cmul
-- statement:
--   The Laurent construction uses the smul cmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L181-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L181-L182

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

theorem GroundTheory.PAdicHodge.Laurent.smul_cmul (k : K) (a b : ℤ → K) : cmul (k • a) b = k • cmul a b := by sorry
