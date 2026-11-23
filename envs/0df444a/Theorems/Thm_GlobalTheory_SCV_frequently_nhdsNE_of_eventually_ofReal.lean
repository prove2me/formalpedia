-- Prove2me | Theorems.Thm_GlobalTheory_SCV_frequently_nhdsNE_of_eventually_ofReal
-- name    : GlobalTheory.SCV.frequently_nhdsNE_of_eventually_ofReal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:35:45.206086+00:00
-- url     : https://prove2.me/theorems/bd84ae9b-b399-4587-a454-21c16317d671
-- title:
--   SCV: frequently nhds NE of eventually of Real
-- statement:
--   The SCV construction uses the frequently nhds NE of eventually of Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EventuallyIteratedFDerivEqZeroOfRealSubspace.lean#L22-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EventuallyIteratedFDerivEqZeroOfRealSubspace.lean#L22-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EventuallyIteratedFDerivEqZeroOfRealSubspace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Set Filter
open scoped Topology
open GlobalTheory GlobalTheory.SCV
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem GlobalTheory.SCV.frequently_nhdsNE_of_eventually_ofReal {p : ℂ → Prop}
    (h : ∀ᶠ t : ℝ in 𝓝 0, p t) : ∃ᶠ t in 𝓝[≠] (0 : ℂ), p t := by sorry
