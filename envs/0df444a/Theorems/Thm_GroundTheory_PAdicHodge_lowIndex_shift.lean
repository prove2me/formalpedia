-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_lowIndex_shift
-- name    : GroundTheory.PAdicHodge.lowIndex_shift
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:29:50.82228+00:00
-- url     : https://prove2.me/theorems/73192a18-9f6c-4a2b-823a-fbdf890b3c1a
-- title:
--   PAdic Hodge: low Index shift
-- statement:
--   The PAdic Hodge construction uses the low Index shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaBounded.lean#L473-L485
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ExtRobbaBounded.lean#L473-L485

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaBounded
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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.PAdicHodge
open Laurent Filter Topology
variable {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] {a : ℤ → L} {ρ : ℝ}

theorem GroundTheory.PAdicHodge.lowIndex_shift (hρ0 : 0 < ρ) (h : ConvergesAt a ρ) (ha : a ≠ 0) (N : ℤ) :
    lowIndex (fun k => a (k + N)) ρ = lowIndex a ρ - N := by sorry
