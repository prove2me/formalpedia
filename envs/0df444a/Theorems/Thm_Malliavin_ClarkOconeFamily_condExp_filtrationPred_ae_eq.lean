-- Prove2me | Theorems.Thm_Malliavin_ClarkOconeFamily_condExp_filtrationPred_ae_eq
-- name    : Malliavin.ClarkOconeFamily.condExp_filtrationPred_ae_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:28:15.392892+00:00
-- url     : https://prove2.me/theorems/67abd076-270e-5417-b65e-b5a5065d9d0e
-- title:
--   Clark Ocone Family: cond Exp filtration Pred ae eq
-- statement:
--   A Clark--Ocone family's natural filtration is left-continuous at the level of conditional
--   expectations.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalFiltrationLeftContinuous.lean#L115-L121
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalFiltrationLeftContinuous.lean#L115-L121

import Definitions.Def_Malliavin_PointwiseCondExp
import Definitions.Def_Malliavin_NaturalFiltrationLeftContinuous
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
variable {B : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}

theorem Malliavin.ClarkOconeFamily.condExp_filtrationPred_ae_eq
    (C : ClarkOconeFamily B P 𝓕) (t : ℝ≥0) (ht : 0 < t)
    (X : W → ℝ) (hX : Integrable X P) :
    P[X | filtrationPred 𝓕 t] =ᵐ[P] P[X | 𝓕 t] := by sorry
