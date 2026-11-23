-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_Laurent_gaussNorm_le
-- name    : GroundTheory.PAdicHodge.Laurent.gaussNorm_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:34:07.307006+00:00
-- url     : https://prove2.me/theorems/7a3c2e05-b5aa-4de3-bbc7-1c002fc4d3aa
-- title:
--   Laurent: gauss Norm le
-- statement:
--   The Laurent construction uses the gauss Norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L41-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L41-L42

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

theorem GroundTheory.PAdicHodge.Laurent.gaussNorm_le {C : ℝ} (h : ∀ n, ‖a n‖ * ρ ^ n ≤ C) : gaussNorm a ρ ≤ C := by sorry
