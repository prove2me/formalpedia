-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_Laurent_ConvergesAt_summable_term
-- name    : GroundTheory.PAdicHodge.Laurent.ConvergesAt.summable_term
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:46:13.154821+00:00
-- url     : https://prove2.me/theorems/e3333d59-61a2-4c4c-b7eb-56968303e971
-- title:
--   Converges At: summable term
-- statement:
--   The Converges At construction uses the summable term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L113-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L113-L115

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

theorem GroundTheory.PAdicHodge.Laurent.ConvergesAt.summable_term [CompleteSpace K] (hρ : 0 < ρ) (ha : ConvergesAt a ρ)
    (hb : ConvergesAt b ρ) (n : ℤ) : Summable (fun i => a i * b (n - i)) := by sorry
