-- Prove2me | Theorems.Thm_Malliavin_ClarkOconeFamily_condExp_brownian_filtrationPred
-- name    : Malliavin.ClarkOconeFamily.condExp_brownian_filtrationPred
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:28:05.752378+00:00
-- url     : https://prove2.me/theorems/d1f39d40-c9ae-4591-af1f-b24ce965bfb7
-- title:
--   Clark Ocone Family: cond Exp brownian filtration Pred
-- statement:
--   **The Brownian coordinate is measurable with respect to its strict past, up to null sets**:
--   `E[B t | 𝓕_{t⁻}] = B t` almost surely, for `t > 0`.  Third brick of the left-continuity
--   capstone: with Lévy's upward theorem the martingale values `B (t - t/(n+2))` converge to
--   `E[B t | 𝓕_{t⁻}]`, while in `L²` they converge to `B t`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L978-L1034
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L978-L1034

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_WienerChaos
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.ConditionalExpectation
import Definitions.Def_Malliavin_PointwiseCondExp
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
variable {B : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
variable {B : ℝ≥0 → W → ℝ}

theorem Malliavin.ClarkOconeFamily.condExp_brownian_filtrationPred
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} (C : ClarkOconeFamily B P 𝓕)
    {t : ℝ≥0} (hat : 0 < t) :
    P[B t | filtrationPred 𝓕 t] =ᵐ[P] B t := by sorry
