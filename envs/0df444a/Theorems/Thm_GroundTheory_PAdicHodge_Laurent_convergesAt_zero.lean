-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_Laurent_convergesAt_zero
-- name    : GroundTheory.PAdicHodge.Laurent.convergesAt_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:45:30.95691+00:00
-- url     : https://prove2.me/theorems/ee1c5160-3dfa-4a65-8a8d-a8f165aa3a49
-- title:
--   Laurent: converges At zero
-- statement:
--   The Laurent construction uses the converges At zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L52-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L52-L53

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

theorem GroundTheory.PAdicHodge.Laurent.convergesAt_zero : ConvergesAt (0 : ℤ → K) ρ := by sorry
