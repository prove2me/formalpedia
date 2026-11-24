-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m87_qpos_interval_density_nonneg
-- name    : Kyprianou.Ch08.StageB.p2m87_qpos_interval_density_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T01:36:43.242001+00:00
-- url     : https://prove2.me/theorems/27622816-0d93-44ab-a398-28a9e8d4d416
-- title:
--   Positive-discount killed interval scale density is nonnegative
-- statement:
--   For q>0, 0<=x<=a and 0<=y<=a, the killed interval resolvent density Wq(x)Wq(a-y)/Wq(a)-Wq(x-y) is nonnegative.
-- source:
--   Source-faithful helper isolated from the positive-discount killed interval density split at pinned revision 0df444a360eaa60ab8c11dca51a86af692955474

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
open Kyprianou.Ch08
open Kyprianou.Ch08.StageB

theorem Kyprianou.Ch08.StageB.p2m87_qpos_interval_density_nonneg :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ (q a x y : ℝ), 0 < q → 0 < a → 0 ≤ x → x ≤ a → 0 ≤ y → y ≤ a →
      0 ≤ killedIntervalDensity (W q) a x y := by sorry
