-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_Laurent_norm_tsum_eq_of_dominant
-- name    : GroundTheory.PAdicHodge.Laurent.norm_tsum_eq_of_dominant
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:45:22.440479+00:00
-- url     : https://prove2.me/theorems/60b7da8b-2929-4f84-a8c1-701045bad0cb
-- title:
--   Laurent: norm tsum eq of dominant
-- statement:
--   The Laurent construction uses the norm tsum eq of dominant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L244-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L244-L261

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

theorem GroundTheory.PAdicHodge.Laurent.norm_tsum_eq_of_dominant [CompleteSpace K] {ι : Type*} {f : ι → K}
    (hf : Tendsto f cofinite (𝓝 0)) (i₀ : ι) (h0 : f i₀ ≠ 0)
    (h : ∀ i, i ≠ i₀ → ‖f i‖ < ‖f i₀‖) : ‖∑' i, f i‖ = ‖f i₀‖ := by sorry
