-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m87_qpos_halfline_density_nonneg
-- name    : Kyprianou.Ch08.StageB.p2m87_qpos_halfline_density_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T01:36:40.094187+00:00
-- url     : https://prove2.me/theorems/b36c7aaa-a7ff-48f4-af6b-0b7737236123
-- title:
--   Positive-discount killed half-line scale density is nonnegative
-- statement:
--   For q>0 and x,y>=0, the killed half-line resolvent density exp(-Phi(q)y)Wq(x)-Wq(x-y) is nonnegative.
-- source:
--   Source-faithful helper isolated from the positive-discount killed interval density split at pinned revision 0df444a360eaa60ab8c11dca51a86af692955474

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
open Kyprianou.Ch08
open Kyprianou.Ch08.StageB

theorem Kyprianou.Ch08.StageB.p2m87_qpos_halfline_density_nonneg :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ (q x y : ℝ), 0 < q → 0 ≤ x → 0 ≤ y →
      0 ≤ killedHalflineDensity ψ q (W q) x y := by sorry
