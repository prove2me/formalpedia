-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_Laurent_ConvergesAt_le_gaussNorm
-- name    : GroundTheory.PAdicHodge.Laurent.ConvergesAt.le_gaussNorm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:34:01.077316+00:00
-- url     : https://prove2.me/theorems/fcc705f8-a1f6-487a-9771-7c2607ee7f44
-- title:
--   Converges At: le gauss Norm
-- statement:
--   The Converges At construction uses the le gauss Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L37-L39

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

theorem GroundTheory.PAdicHodge.Laurent.ConvergesAt.le_gaussNorm (h : ConvergesAt a ρ) (n : ℤ) :
    ‖a n‖ * ρ ^ n ≤ gaussNorm a ρ := by sorry
