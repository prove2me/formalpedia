-- Prove2me | Theorems.Thm_Malliavin_natural_eq_filtrationPred_sup
-- name    : Malliavin.natural_eq_filtrationPred_sup
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:27:42.682897+00:00
-- url     : https://prove2.me/theorems/d52e0f9f-9b6d-4606-80d6-f184dc2379ad
-- title:
--   Malliavin: natural eq filtration Pred sup
-- statement:
--   The natural filtration at `t` splits as the strict past joined with the time-`t`
--   coordinate.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L848-L863
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L848-L863

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
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
  [SecondCountableTopology W] [IsGaussian P]

theorem Malliavin.natural_eq_filtrationPred_sup (hm : ∀ s, StronglyMeasurable (B s)) (t : ℝ≥0) :
    Filtration.natural B hm t
      = filtrationPred (Filtration.natural B hm) t
        ⊔ MeasurableSpace.comap (B t) inferInstance := by sorry
