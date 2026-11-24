-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m87_qpos_interval_density_halfline_add_split
-- name    : Kyprianou.Ch08.StageB.p2m87_qpos_interval_density_halfline_add_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T00:35:15.238066+00:00
-- url     : https://prove2.me/theorems/1b81a72a-608e-4e15-8a0f-a77dc0c4be76
-- title:
--   Positive-discount killed interval density splits the two half-line densities
-- statement:
--   For 0<q and 0<=x<=a, the killed interval density measure on [0,a] and the q-scale exit ratio W(q,x)/W(q,a) add to the killed half-line density measure started at x. This is the purely analytic half of the positive-discount interval occupation bridge.
-- source:
--   Source-faithful split of exact bridge target dd94395e-5a1b-4371-8a44-53bb6ca85201 at pinned revision 0df444a360eaa60ab8c11dca51a86af692955474

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
open Kyprianou.Ch08
open Kyprianou.Ch08.StageB

theorem Kyprianou.Ch08.StageB.p2m87_qpos_interval_density_halfline_add_split :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ (q a x : ℝ), 0 < q → 0 < a → 0 ≤ x → x ≤ a →
      ∀ (A : Set ℝ), MeasurableSet A →
        ((volume.restrict (Set.Ici (0 : ℝ))).withDensity
          (fun y : ℝ => ENNReal.ofReal
            (killedHalflineDensity ψ q (W q) x y))) A =
        ((volume.restrict (Set.Icc 0 a)).withDensity
          (fun y : ℝ => ENNReal.ofReal
            (killedIntervalDensity (W q) a x y))) A +
        ENNReal.ofReal (W q x / W q a) *
          ((volume.restrict (Set.Ici (0 : ℝ))).withDensity
            (fun y : ℝ => ENNReal.ofReal
              (killedHalflineDensity ψ q (W q) a y))) A := by sorry
