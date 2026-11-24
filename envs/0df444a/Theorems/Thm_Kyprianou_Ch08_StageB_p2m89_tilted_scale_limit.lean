-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_tilted_scale_limit
-- name    : Kyprianou.Ch08.StageB.p2m89_tilted_scale_limit
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T08:18:51.745902+00:00
-- url     : https://prove2.me/theorems/b307a65d-60a2-457f-8b82-5e03a431fb4f
-- title:
--   Tilted scale monotonicity and exact limit
-- statement:
--   Identify the Esscher tilted scale with the cumulative descending potential and its exact total mass.
-- source:
--   Kyprianou (2006), Corollary 8.9; corrected occupation identity 33cf8321-6b73-409d-84cc-a8da6fcb2949.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

open Kyprianou.Ch08 Kyprianou.Ch08.StageB Topology

theorem Kyprianou.Ch08.StageB.p2m89_tilted_scale_limit
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 < q) :
    Monotone (fun r : ℝ => Real.exp (-(Phi ψ q) * r) * W q r) ∧ Tendsto (fun r : ℝ => Real.exp (-(Phi ψ q) * r) * W q r) atTop (𝓝 (deriv (Phi ψ) q)) := by
  sorry
