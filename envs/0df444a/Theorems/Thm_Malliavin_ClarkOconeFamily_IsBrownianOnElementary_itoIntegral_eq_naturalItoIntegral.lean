-- Prove2me | Theorems.Thm_Malliavin_ClarkOconeFamily_IsBrownianOnElementary_itoIntegral_eq_naturalItoIntegral
-- name    : Malliavin.ClarkOconeFamily.IsBrownianOnElementary.itoIntegral_eq_naturalItoIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:40:40.90564+00:00
-- url     : https://prove2.me/theorems/0aaedaed-b4c8-4b1f-bfe7-dfa2040a72f8
-- title:
--   Is Brownian On Elementary: ito Integral eq natural Ito Integral
-- statement:
--   Any abstract family compatible with elementary Brownian integration uses exactly the
--   constructed natural-filtration Itô integral.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ItoConstruction.lean#L501-L515
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ItoConstruction.lean#L501-L515

import Definitions.Def_Malliavin_ElementaryIto
import Definitions.Def_Malliavin_PredictableDensity
import Definitions.Def_Malliavin_ItoConstruction
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}

theorem Malliavin.ClarkOconeFamily.IsBrownianOnElementary.itoIntegral_eq_naturalItoIntegral
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} {C : ClarkOconeFamily B P 𝓕}
    (hC : C.IsBrownianOnElementary) :
    C.itoIntegral =
      naturalItoIntegral C.isPreBrownian C.stronglyMeasurable C.naturalFiltration := by sorry
