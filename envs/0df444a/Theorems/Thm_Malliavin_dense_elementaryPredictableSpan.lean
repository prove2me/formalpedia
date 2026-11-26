-- Prove2me | Theorems.Thm_Malliavin_dense_elementaryPredictableSpan
-- name    : Malliavin.dense_elementaryPredictableSpan
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:13:51.98705+00:00
-- url     : https://prove2.me/theorems/2a9fb431-9277-52c4-a983-936388ec4f23
-- title:
--   Malliavin: dense elementary Predictable Span
-- statement:
--   Finite linear combinations of one-step adapted processes are dense in predictable `L²`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PredictableDensity.lean#L395-L410
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PredictableDensity.lean#L395-L410

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_PredictableDensity
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Function
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
omit [CompleteSpace W] [BorelSpace W]

theorem Malliavin.dense_elementaryPredictableSpan
    (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace W)) :
    Dense (elementaryPredictableSpan (P := P) 𝓕 :
      Set (PredictableProcessL2 𝓕 P)) := by sorry
