-- Prove2me | Theorems.Thm_Malliavin_ae_eq_zero_of_orthogonal_elementaryPredictable
-- name    : Malliavin.ae_eq_zero_of_orthogonal_elementaryPredictable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:24:16.99006+00:00
-- url     : https://prove2.me/theorems/3dabdb1c-afe5-44be-83ad-85ae97a5e27f
-- title:
--   Malliavin: ae eq zero of orthogonal elementary Predictable
-- statement:
--   A predictable process orthogonal to every one-step adapted process vanishes almost
--   everywhere.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PredictableDensity.lean#L378-L391
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PredictableDensity.lean#L378-L391

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

theorem Malliavin.ae_eq_zero_of_orthogonal_elementaryPredictable
    (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace W))
    (g : PredictableProcessL2 𝓕 P)
    (horth : ∀ U : PredictableProcessL2 𝓕 P,
      U ∈ elementaryPredictableSpan (P := P) 𝓕 → ⟪U, g⟫_ℝ = 0) :
    (g : ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P] 0 := by sorry
