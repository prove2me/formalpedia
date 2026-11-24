-- Prove2me | Theorems.Thm_GlobalTheory_tendsto_tsum_coeff_mul_pow_zero
-- name    : GlobalTheory.tendsto_tsum_coeff_mul_pow_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:24:26.019907+00:00
-- url     : https://prove2.me/theorems/4954446a-fd8e-417d-92c2-d8f034cfdac4
-- title:
--   Global Theory: tendsto tsum coeff mul pow zero
-- statement:
--   The Global Theory construction uses the tendsto tsum coeff mul pow zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DetBoundedConvergentPowerSeriesMatrixETwoPi.lean#L9-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DetBoundedConvergentPowerSeriesMatrixETwoPi.lean#L9-L30

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DetBoundedConvergentPowerSeriesMatrixETwoPi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open Filter Topology

theorem GlobalTheory.tendsto_tsum_coeff_mul_pow_zero (a : ℕ → ℂ) (q₀ : ℂ) (hq₀ : q₀ ≠ 0)
    (hs : Summable (fun m : ℕ => a m * q₀ ^ m)) :
    Tendsto (fun q : ℂ => ∑' m : ℕ, a m * q ^ m) (𝓝 0) (𝓝 (a 0)) := by sorry
