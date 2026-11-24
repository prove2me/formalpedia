-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_source_scale_cumulative
-- name    : Kyprianou.Ch08.StageB.p2m89_source_scale_cumulative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T09:52:34.659171+00:00
-- url     : https://prove2.me/theorems/968d214f-5547-4692-892e-b610175a1e29
-- title:
--   Identify tilted source scale with descending potential
-- statement:
--   Use the established tilted descending potential and uniqueness of the scale Laplace transform on the positive half-line, extending to zero by continuity.
-- source:
--   Kyprianou (2006), Corollary 8.9; exact decomposition of b307a65d-60a2-457f-8b82-5e03a431fb4f.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

open Kyprianou.Ch08 Kyprianou.Ch08.StageB Topology

theorem Kyprianou.Ch08.StageB.p2m89_source_scale_cumulative
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 < q) :
    ∃ ν : Measure ℝ, ν (Iio (0 : ℝ)) = 0 ∧
      (∀ r : ℝ, ν (Iic r) < ⊤) ∧
      (∀ s : ℝ, 0 < s → (∫⁻ y, ENNReal.ofReal (Real.exp (-s*y)) ∂ν) =
        ENNReal.ofReal (s / (ψ (Phi ψ q + s) - q))) ∧
      (∀ r : ℝ, Real.exp (-(Phi ψ q) * r) * W q r = (ν (Iic r)).toReal) := by
  sorry
