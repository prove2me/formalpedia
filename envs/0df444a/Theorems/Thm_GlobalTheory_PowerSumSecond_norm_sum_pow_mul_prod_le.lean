-- Prove2me | Theorems.Thm_GlobalTheory_PowerSumSecond_norm_sum_pow_mul_prod_le
-- name    : GlobalTheory.PowerSumSecond.norm_sum_pow_mul_prod_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:54:13.310725+00:00
-- url     : https://prove2.me/theorems/2844ecaa-4fff-4114-b644-f37978296c18
-- title:
--   Power Sum Second: norm sum pow mul prod le
-- statement:
--   The Power Sum Second construction uses the norm sum pow mul prod le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TuranSecondMainTheoremPowerSumsUnitCoefficients.lean#L9-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TuranSecondMainTheoremPowerSumsUnitCoefficients.lean#L9-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsProdAbsSubGeOnSegment
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsInterpolationExteriorSmallCoeffsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TuranSecondMainTheoremPowerSumsUnitCoefficients
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory
open GlobalTheory.PowerSumSecond

theorem GlobalTheory.PowerSumSecond.norm_sum_pow_mul_prod_le {ι κ : Type*} [Fintype ι] (z : ι → ℂ) (a : κ → ℂ) (B : ℝ)
    (T : Finset κ) (ha : ∀ t ∈ T, ‖a t‖ ≤ 1) :
    ∀ m : ℕ, (∀ k, m ≤ k → k ≤ m + T.card → ‖∑ i, z i ^ k‖ ≤ B) →
      ‖∑ i, z i ^ m * ∏ t ∈ T, (z i - a t)‖ ≤ 2 ^ T.card * B := by sorry
