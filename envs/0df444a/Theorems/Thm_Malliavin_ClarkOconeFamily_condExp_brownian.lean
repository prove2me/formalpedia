-- Prove2me | Theorems.Thm_Malliavin_ClarkOconeFamily_condExp_brownian
-- name    : Malliavin.ClarkOconeFamily.condExp_brownian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:27:52.068789+00:00
-- url     : https://prove2.me/theorems/c5372df8-27ea-5772-9ed8-54ace0453643
-- title:
--   Clark Ocone Family: cond Exp brownian
-- statement:
--   **The pre-Brownian martingale property**: `E[B b | 𝓕 a] = B a` for `a ≤ b`, over any
--   Clark--Ocone family.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L912-L972
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L912-L972

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

theorem Malliavin.ClarkOconeFamily.condExp_brownian
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} (C : ClarkOconeFamily B P 𝓕)
    {a b : ℝ≥0} (hab : a ≤ b) :
    P[B b | 𝓕 a] =ᵐ[P] B a := by sorry
