-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_Laurent_norm_tsum_lt
-- name    : GroundTheory.PAdicHodge.Laurent.norm_tsum_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:39.803224+00:00
-- url     : https://prove2.me/theorems/b306101b-429f-4cd3-8c09-f7315119ecc9
-- title:
--   Laurent: norm tsum lt
-- statement:
--   The Laurent construction uses the norm tsum lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L224-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/RobbaSeries.lean#L224-L242

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

theorem GroundTheory.PAdicHodge.Laurent.norm_tsum_lt {ι : Type*} {f : ι → K} (hf : Tendsto f cofinite (𝓝 0)) {M : ℝ}
    (hM : 0 < M) (h : ∀ i, ‖f i‖ < M) : ‖∑' i, f i‖ < M := by sorry
