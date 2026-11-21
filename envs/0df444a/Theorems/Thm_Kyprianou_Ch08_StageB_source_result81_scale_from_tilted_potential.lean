-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_scale_from_tilted_potential
-- name    : Kyprianou.Ch08.StageB.source_result81_scale_from_tilted_potential
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T20:40:08.989579+00:00
-- url     : https://prove2.me/theorems/40899fa3-08db-48e0-88dd-e4cea3055bc5
-- title:
--   Normalize a scale function from its tilted descending potential
-- statement:
--   The scale function is the exponential untilt of the cumulative descending potential. Continuity of the cumulative values at each positive location follows from absence of atoms there. Tonelli and the exponential integral over the corresponding right ray give the inverse normalization.
-- source:
--   Kyprianou (2006), Chapter 8, Theorem 8.1. Source-faithful decomposition of b5430c32-5738-4ad5-9956-e8891a1d6407.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_scale_from_tilted_potential
    (ψ : ℝ → ℝ) (q : ℝ) (hroot : IsScaleTransformDomainBridge ψ q)
    (ν : Measure ℝ) (hsupp : ν (Iio (0 : ℝ)) = 0)
    (hfin : ∀ x : ℝ, 0 ≤ x → ν (Iic x) < ⊤)
    (hatom : ∀ x : ℝ, 0 < x → ν {x} = 0)
    (hlap : ∀ s : ℝ, 0 < s →
      (∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂ν) =
        ENNReal.ofReal (s / (ψ (Phi ψ q + s) - q))) :
    ∃ w : ℝ → ℝ, IsQScale ψ q w := by
  sorry
