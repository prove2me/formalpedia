-- Prove2me | Theorems.Thm_Malliavin_condExpKernel_predictable_map_fst_ae
-- name    : Malliavin.condExpKernel_predictable_map_fst_ae
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:33:16.026531+00:00
-- url     : https://prove2.me/theorems/cab4efab-f37f-5104-8cdc-ef14d3431683
-- title:
--   Malliavin: cond Exp Kernel predictable map fst ae
-- statement:
--   Kernel-valued form of `condExpKernel_predictable_ae_same_time`: pushing the predictable
--   conditional kernel forward by the time coordinate gives the Dirac kernel at the observed time.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PredictableKernel.lean#L111-L118
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PredictableKernel.lean#L111-L118

import Definitions.Def_Malliavin_ClarkOcone
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Kernel.Composition.MapComap
import Definitions.Def_Malliavin_PredictableKernel
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
variable {S : Type*} [MeasurableSpace S] [StandardBorelSpace S]

theorem Malliavin.condExpKernel_predictable_map_fst_ae
    (μ : Measure (ℝ≥0 × S)) [IsFiniteMeasure μ]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace S›) :
    (condExpKernel μ 𝓕.predictable).map Prod.fst =ᵐ[μ]
      Kernel.deterministic Prod.fst (measurable_fst_predictable 𝓕) := by sorry
