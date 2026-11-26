-- Prove2me | Theorems.Thm_Malliavin_integral_predictableProjection_Ioc
-- name    : Malliavin.integral_predictableProjection_Ioc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:20:46.944351+00:00
-- url     : https://prove2.me/theorems/e4ede41e-cd8a-4b7c-a5d3-c60b67cfd724
-- title:
--   Malliavin: integral predictable Projection Ioc
-- statement:
--   Predictable projection preserves integrals over predictable rectangles
--   `(a, b] × A` with `A ∈ 𝓕_a`.  This is the product-space conditional-expectation identity
--   available without choosing pointwise time sections.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOcone.lean#L290-L310
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOcone.lean#L290-L310

import Definitions.Def_Malliavin_TimeDerivative
import Mathlib.Probability.Process.Predictable
import Definitions.Def_Malliavin_ClarkOcone
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [CompleteSpace W] [BorelSpace W]

theorem Malliavin.integral_predictableProjection_Ioc
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (U : TimeProcessL2 P) (a b : ℝ≥0) {A : Set W}
    (hA : MeasurableSet[𝓕 a] A) :
    ∫ t in Set.Ioc a b, ∫ ω in A,
        (predictableProjection 𝓕 U : (ℝ≥0 × W) → ℝ) (t, ω) ∂P
        ∂nonnegativeLebesgueMeasure =
      ∫ t in Set.Ioc a b, ∫ ω in A, U (t, ω) ∂P
        ∂nonnegativeLebesgueMeasure := by sorry
