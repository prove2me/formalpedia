-- Prove2me | Theorems.Thm_GlobalTheory_exists_eq_const_of_periodic_of_simple_pole
-- name    : GlobalTheory.exists_eq_const_of_periodic_of_simple_pole
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:31:32.645032+00:00
-- url     : https://prove2.me/theorems/d2639377-398c-45ba-b487-b058bcbd8acb
-- title:
--   Global Theory: exists eq const of periodic of simple pole
-- statement:
--   The Global Theory construction uses the exists eq const of periodic of simple pole property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L1216-L1272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L1216-L1272

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

theorem GlobalTheory.exists_eq_const_of_periodic_of_simple_pole {f N : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (L.lattice : Set ℂ)ᶜ)
    (hper : ∀ z ∉ L.lattice, ∀ w ∈ L.lattice, f (z + w) = f z)
    (hN : AnalyticAt ℂ N 0) (hfN : ∀ᶠ z in 𝓝[≠] 0, z * f z = N z) :
    ∃ c, ∀ z ∉ L.lattice, f z = c := by sorry
