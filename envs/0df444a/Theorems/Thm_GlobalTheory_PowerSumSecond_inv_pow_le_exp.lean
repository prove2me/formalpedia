-- Prove2me | Theorems.Thm_GlobalTheory_PowerSumSecond_inv_pow_le_exp
-- name    : GlobalTheory.PowerSumSecond.inv_pow_le_exp
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:53:53.12811+00:00
-- url     : https://prove2.me/theorems/4ba69501-f78b-4cb6-8783-818a9ca8fe62
-- title:
--   Power Sum Second: inv pow le exp
-- statement:
--   The Power Sum Second construction uses the inv pow le exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TuranSecondMainTheoremPowerSumsUnitCoefficients.lean#L56-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TuranSecondMainTheoremPowerSumsUnitCoefficients.lean#L56-L80

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

theorem GlobalTheory.PowerSumSecond.inv_pow_le_exp (N M : ℕ) (hN : 0 < N) (r : ℝ) (hr : 1 - (N : ℝ) / (2 * (M + N)) ≤ r) :
    1 ≤ r ^ M * Real.exp 1 ^ N := by sorry
