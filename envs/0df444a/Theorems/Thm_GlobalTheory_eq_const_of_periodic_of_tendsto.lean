-- Prove2me | Theorems.Thm_GlobalTheory_eq_const_of_periodic_of_tendsto
-- name    : GlobalTheory.eq_const_of_periodic_of_tendsto
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:29.671809+00:00
-- url     : https://prove2.me/theorems/79762e15-97cf-44b2-9a19-0baf70043e97
-- title:
--   Global Theory: eq const of periodic of tendsto
-- statement:
--   The Global Theory construction uses the eq const of periodic of tendsto property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L1086-L1117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L1086-L1117

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Complex PeriodPair
open scoped Topology ComplexConjugate Real
open GlobalTheory
variable (L : PeriodPair)

theorem GlobalTheory.eq_const_of_periodic_of_tendsto {f : ℂ → ℂ} {c : ℂ}
    (hf : DifferentiableOn ℂ f (L.lattice : Set ℂ)ᶜ)
    (hper : ∀ z ∉ L.lattice, ∀ w ∈ L.lattice, f (z + w) = f z)
    (hc : Tendsto f (𝓝[≠] 0) (𝓝 c)) {z : ℂ} (hz : z ∉ L.lattice) : f z = c := by sorry
