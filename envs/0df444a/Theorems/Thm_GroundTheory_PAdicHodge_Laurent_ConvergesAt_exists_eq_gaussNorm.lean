-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_Laurent_ConvergesAt_exists_eq_gaussNorm
-- name    : GroundTheory.PAdicHodge.Laurent.ConvergesAt.exists_eq_gaussNorm
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:49:25.230574+00:00
-- url     : https://prove2.me/theorems/57355169-f767-453b-ae32-924c36199a39
-- title:
--   Converges At: exists eq gauss Norm
-- statement:
--   The Converges At construction uses the exists eq gauss Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L268-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L268-L278

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
variable (hρ : 0 < ρ) (h : ConvergesAt a ρ) (ha : a ≠ 0)
include hρ h ha

theorem GroundTheory.PAdicHodge.Laurent.ConvergesAt.exists_eq_gaussNorm : ∃ n, ‖a n‖ * ρ ^ n = gaussNorm a ρ := by sorry
