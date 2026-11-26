-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_Laurent_ConvergesAt_of_le_of_le
-- name    : GroundTheory.PAdicHodge.Laurent.ConvergesAt.of_le_of_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:01:01.596351+00:00
-- url     : https://prove2.me/theorems/a3ce5023-a903-4236-8b88-e79af4948045
-- title:
--   Converges At: of le of le
-- statement:
--   The Converges At construction uses the of le of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L72-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L72-L88

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

theorem GroundTheory.PAdicHodge.Laurent.ConvergesAt.of_le_of_le {ρ₁ ρ₂ : ℝ} (h₁ : ConvergesAt a ρ₁) (h₂ : ConvergesAt a ρ₂)
    (hρ₁ : 0 < ρ₁) (h1 : ρ₁ ≤ ρ) (h2 : ρ ≤ ρ₂) : ConvergesAt a ρ := by sorry
