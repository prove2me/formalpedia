-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_Laurent_gaussNorm_cmul
-- name    : GroundTheory.PAdicHodge.Laurent.gaussNorm_cmul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:12.956634+00:00
-- url     : https://prove2.me/theorems/4b7576a9-f732-4311-86c7-99cf98441d0a
-- title:
--   Laurent: gauss Norm cmul
-- statement:
--   The Laurent construction uses the gauss Norm cmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L418-L423
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L418-L423

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
variable (hρ : 0 < ρ) (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
include hρ ha hb ha0 hb0

theorem GroundTheory.PAdicHodge.Laurent.gaussNorm_cmul : gaussNorm (cmul a b) ρ = gaussNorm a ρ * gaussNorm b ρ := by sorry
