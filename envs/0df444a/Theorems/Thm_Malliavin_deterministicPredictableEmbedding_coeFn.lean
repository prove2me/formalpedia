-- Prove2me | Theorems.Thm_Malliavin_deterministicPredictableEmbedding_coeFn
-- name    : Malliavin.deterministicPredictableEmbedding_coeFn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:20:27.575509+00:00
-- url     : https://prove2.me/theorems/93cf23d0-85ac-4039-bba5-3940f97ef7a4
-- title:
--   Malliavin: deterministic Predictable Embedding coe Fn
-- statement:
--   A deterministic predictable integrand represents the function `(t, ω) ↦ f t`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOcone.lean#L139-L144
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOcone.lean#L139-L144

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

theorem Malliavin.deterministicPredictableEmbedding_coeFn
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    (deterministicPredictableEmbedding (P := P) 𝓕 f : (ℝ≥0 × W) → ℝ) =ᵐ[
      nonnegativeLebesgueMeasure.prod P] (f : ℝ≥0 → ℝ) ∘ Prod.fst := by sorry
