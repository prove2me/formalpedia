-- Prove2me | Theorems.Thm_Malliavin_elementaryPredictable_adaptedOne
-- name    : Malliavin.elementaryPredictable_adaptedOne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:18:27.242536+00:00
-- url     : https://prove2.me/theorems/5aba797b-1ce4-49d1-811d-8179e0a34959
-- title:
--   Malliavin: elementary Predictable adapted One
-- statement:
--   The one-step process with constant coefficient `1` on `(0,t]` is the deterministic
--   predictable embedding of `intervalIndicator t`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOcone.lean#L263-L278
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOcone.lean#L263-L278

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

theorem Malliavin.elementaryPredictable_adaptedOne
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (t : ℝ≥0) :
    elementaryPredictable (P := P) 𝓕 0 t (adaptedOne (P := P) 𝓕 0) =
      deterministicPredictableEmbedding 𝓕 (intervalIndicator t) := by sorry
