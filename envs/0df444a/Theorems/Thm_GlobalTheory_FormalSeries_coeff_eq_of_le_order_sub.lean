-- Prove2me | Theorems.Thm_GlobalTheory_FormalSeries_coeff_eq_of_le_order_sub
-- name    : GlobalTheory.FormalSeries.coeff_eq_of_le_order_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:46:05.437804+00:00
-- url     : https://prove2.me/theorems/74d25ece-7733-4396-8a19-0578f81277ce
-- title:
--   Formal Series: coeff eq of le order sub
-- statement:
--   The Formal Series construction uses the coeff eq of le order sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EqZeroOrSingleOfDegreeLtTwo.lean#L35-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EqZeroOrSingleOfDegreeLtTwo.lean#L35-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EqZeroOrSingleOfDegreeLtTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open GlobalTheory.FormalSeries
open MvPowerSeries
variable {σ τ υ R S : Type*} [CommRing R] [CommRing S]

theorem GlobalTheory.FormalSeries.coeff_eq_of_le_order_sub {k : ℕ} {f g : MvPowerSeries σ R} (h : (k : ℕ∞) ≤ (f - g).order)
    {d : σ →₀ ℕ} (hd : d.degree < k) : coeff d f = coeff d g := by sorry
