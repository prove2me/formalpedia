-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_tilted_cumulative_laplace
-- name    : Kyprianou.Ch08.StageB.source_result81_tilted_cumulative_laplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T11:36:30.850117+00:00
-- url     : https://prove2.me/theorems/8cf386e6-2787-453c-bb8a-9b75f14ca648
-- title:
--   Laplace transform of the untilted cumulative potential
-- statement:
--   Let the Laplace transform of a nonnegative potential measure be s divided by the shifted Lévy exponent at s. Multiplying its real cumulative mass by the exponential at the largest root gives an integrable Laplace integrand at every parameter above the root, with integral equal to the reciprocal of the original exponent minus the discount.
-- source:
--   Kyprianou (2006), Chapter 8, Theorem 8.1, construction from a tilted descending potential. Auxiliary obligation of 40899fa3-08db-48e0-88dd-e4cea3055bc5.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_tilted_cumulative_laplace
    (ψ : ℝ → ℝ) (q : ℝ) (hroot : IsScaleTransformDomainBridge ψ q)
    (ν : Measure ℝ) (hsupp : ν (Iio (0 : ℝ)) = 0)
    (hf : ∀ x : ℝ, ν (Iic x) < ⊤)
    (hlap : ∀ s : ℝ, 0 < s →
      (∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂ν) =
        ENNReal.ofReal (s / (ψ (Phi ψ q + s) - q))) :
    ∀ β : ℝ, 0 ≤ β → Phi ψ q < β →
      IntegrableOn
        (fun x => Real.exp (-β * x) * (Real.exp (Phi ψ q * x) * (ν (Iic x)).toReal))
        (Ioi 0) volume ∧
      (∫ x in Ioi 0, Real.exp (-β * x) * (Real.exp (Phi ψ q * x) * (ν (Iic x)).toReal)) =
        (ψ β - q)⁻¹ := by
  sorry
