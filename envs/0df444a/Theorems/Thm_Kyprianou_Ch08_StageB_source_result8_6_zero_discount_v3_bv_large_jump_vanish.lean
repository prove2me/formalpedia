-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_zero_discount_v3_bv_large_jump_vanish
-- name    : Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_bv_large_jump_vanish
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T19:24:12.677667+00:00
-- url     : https://prove2.me/theorems/8d97af26-367b-4795-8385-9682980b9177
-- title:
--   Large-jump compensated quotient vanishes
-- statement:
--   On jumps at most minus one, the compensated exponential quotient is bounded by one and converges pointwise to zero, so Levy quadratic integrability gives convergence of its integral to zero.
-- source:
--   Lemma 8.6 corrected proof: dominated convergence on Iic (-1).

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_bv_large_jump_vanish :
    ∀ (Ω : Type) [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P),
      Tendsto (fun β : ℝ => ∫ x in Set.Iic (-1 : ℝ),
        ((Real.exp (β * x) - 1) / β) ∂D.triplet.levyMeasure) atTop (𝓝 0) := by sorry
