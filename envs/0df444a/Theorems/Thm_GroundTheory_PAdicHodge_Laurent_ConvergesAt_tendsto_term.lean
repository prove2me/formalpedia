-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_Laurent_ConvergesAt_tendsto_term
-- name    : GroundTheory.PAdicHodge.Laurent.ConvergesAt.tendsto_term
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:34:52.098555+00:00
-- url     : https://prove2.me/theorems/1d63d791-4017-401f-9dc6-9ae8d62a23a5
-- title:
--   Converges At: tendsto term
-- statement:
--   The Converges At construction uses the tendsto term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L104-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L104-L111

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

theorem GroundTheory.PAdicHodge.Laurent.ConvergesAt.tendsto_term (hρ : 0 < ρ) (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ)
    (n : ℤ) : Tendsto (fun i => a i * b (n - i)) cofinite (𝓝 0) := by sorry
