-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_Laurent_ConvergesAt_add
-- name    : GroundTheory.PAdicHodge.Laurent.ConvergesAt.add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:38.947179+00:00
-- url     : https://prove2.me/theorems/4b8efa20-5e29-4aac-9f14-af06b2cf3ade
-- title:
--   Converges At: add
-- statement:
--   The Converges At construction uses the add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L55-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L55-L60

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

theorem GroundTheory.PAdicHodge.Laurent.ConvergesAt.add (hρ : 0 < ρ) (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ) :
    ConvergesAt (a + b) ρ := by sorry
