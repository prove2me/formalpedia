-- Prove2me | Theorems.Thm_GlobalTheory_PowerSumSecond_tendsto_inv_prod
-- name    : GlobalTheory.PowerSumSecond.tendsto_inv_prod
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:54:05.904911+00:00
-- url     : https://prove2.me/theorems/238ec173-5554-4605-b89e-7352c42b8088
-- title:
--   Power Sum Second: tendsto inv prod
-- statement:
--   The Power Sum Second construction uses the tendsto inv prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TuranSecondMainTheoremPowerSumsUnitCoefficients.lean#L38-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TuranSecondMainTheoremPowerSumsUnitCoefficients.lean#L38-L54

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

theorem GlobalTheory.PowerSumSecond.tendsto_inv_prod {κ : Type*} (a : κ → ℂ) (T : Finset κ) (ha : ∀ t ∈ T, ‖a t‖ ≤ 1) (M : ℕ) :
    Tendsto (fun w : ℂ => (w ^ (M + 1) * ∏ t ∈ T, (w - a t))⁻¹) (Filter.cocompact ℂ) (𝓝 0) := by sorry
