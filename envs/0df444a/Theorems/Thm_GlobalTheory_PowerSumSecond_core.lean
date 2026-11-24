-- Prove2me | Theorems.Thm_GlobalTheory_PowerSumSecond_core
-- name    : GlobalTheory.PowerSumSecond.core
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:42:30.717344+00:00
-- url     : https://prove2.me/theorems/22a4d53e-1bda-4a2b-a74b-e05ac928da7b
-- title:
--   Power Sum Second: core
-- statement:
--   The Power Sum Second construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TuranSecondMainTheoremPowerSumsUnitCoefficients.lean#L82-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TuranSecondMainTheoremPowerSumsUnitCoefficients.lean#L82-L199

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

theorem GlobalTheory.PowerSumSecond.core (N M : ℕ) (z : Fin N → ℂ) (i₁ : Fin N) (h1 : ‖z i₁‖ = 1) (hz : ∀ i, ‖z i‖ ≤ 1)
    (B : ℝ) (hB : ∀ k, M + 1 ≤ k → k ≤ M + N → ‖∑ i, z i ^ k‖ ≤ B) :
    ((N : ℝ) / (16 * Real.exp 1 ^ 2 * (M + N))) ^ N ≤ B := by sorry
