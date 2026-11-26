-- Prove2me | Theorems.Thm_Malliavin_condExp_natural_filtrationPred_ae_eq
-- name    : Malliavin.condExp_natural_filtrationPred_ae_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:19:44.518702+00:00
-- url     : https://prove2.me/theorems/e0444791-084b-5f4d-9139-d95256350a85
-- title:
--   Malliavin: cond Exp natural filtration Pred ae eq
-- statement:
--   **Left-continuity modulo `P` of the natural Brownian filtration.**
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalFiltrationLeftContinuous.lean#L89-L107
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalFiltrationLeftContinuous.lean#L89-L107

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
omit [CompleteSpace W] [BorelSpace W]

theorem Malliavin.condExp_natural_filtrationPred_ae_eq
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hm : ∀ s, StronglyMeasurable (B s)) (t : ℝ≥0) (ht : 0 < t)
    (X : W → ℝ) (hX : Integrable X P) :
    P[X | filtrationPred (Filtration.natural B hm) t] =ᵐ[P]
      P[X | Filtration.natural B hm t] := by sorry
