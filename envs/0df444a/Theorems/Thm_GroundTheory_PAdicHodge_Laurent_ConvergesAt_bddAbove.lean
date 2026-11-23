-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_Laurent_ConvergesAt_bddAbove
-- name    : GroundTheory.PAdicHodge.Laurent.ConvergesAt.bddAbove
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:34:26.538312+00:00
-- url     : https://prove2.me/theorems/e8a9236d-b046-4533-a18b-6e5a38eaae8a
-- title:
--   Converges At: bdd Above
-- statement:
--   The Converges At construction uses the bdd Above property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L33-L35

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

theorem GroundTheory.PAdicHodge.Laurent.ConvergesAt.bddAbove (h : ConvergesAt a ρ) :
    BddAbove (Set.range fun n : ℤ => ‖a n‖ * ρ ^ n) := by sorry
