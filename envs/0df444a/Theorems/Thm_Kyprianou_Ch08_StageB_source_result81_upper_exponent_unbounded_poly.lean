-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_upper_exponent_unbounded_poly
-- name    : Kyprianou.Ch08.StageB.source_result81_upper_exponent_unbounded_poly
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T19:45:34.882698+00:00
-- url     : https://prove2.me/theorems/44a8516c-285c-4ee3-a538-2c4b5fa142ef
-- title:
--   Unbounded Laplace exponent from a positive marginal at arbitrary universes
-- statement:
--   The accepted Chapter 8 unbounded-exponent lemma generalized to an arbitrary sample-space universe. A positive marginal at one time forces the Laplace exponent to exceed any prescribed real level at some positive argument.
-- source:
--   Kyprianou (2006), Chapter 8, Theorem 8.1. Source-faithful universe-polymorphic version of the accepted source_result81_levy_exponent_unbounded, needed by the public scale-transfer child because the existing helper is fixed to Ω : Type.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Positivity
open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_upper_exponent_unbounded_poly
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} (A : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    {t : ℝ≥0} (ht : ¬ (∀ᵐ ω ∂P, A.X t ω ≤ 0)) (q : ℝ) :
    ∃ b : ℝ, 0 < b ∧ q < A.ψ b := by sorry
