-- Prove2me | Theorems.Thm_Malliavin_condExp_filtrationPred_ae_eq_of_ae_sets
-- name    : Malliavin.condExp_filtrationPred_ae_eq_of_ae_sets
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:28:31.257365+00:00
-- url     : https://prove2.me/theorems/b6ba004f-686b-4fc5-a7aa-680ffaa21c00
-- title:
--   Malliavin: cond Exp filtration Pred ae eq of ae sets
-- statement:
--   If every event at time `t` has a strict-past-measurable representative modulo `P`, then
--   conditioning on the strict past and conditioning at `t` agree.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalFiltrationLeftContinuous.lean#L39-L57
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalFiltrationLeftContinuous.lean#L39-L57

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

theorem Malliavin.condExp_filtrationPred_ae_eq_of_ae_sets
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (t : ℝ≥0)
    (hcomplete : ∀ s : Set W, MeasurableSet[𝓕 t] s →
      ∃ r : Set W, MeasurableSet[filtrationPred 𝓕 t] r ∧ s =ᵐ[P] r)
    (X : W → ℝ) (hX : Integrable X P) :
    P[X | filtrationPred 𝓕 t] =ᵐ[P] P[X | 𝓕 t] := by sorry
