-- Prove2me | Theorems.Thm_Malliavin_ClarkOconeFamily_isBrownianOnElementary_iff_itoIntegral_eq_naturalItoIntegral
-- name    : Malliavin.ClarkOconeFamily.isBrownianOnElementary_iff_itoIntegral_eq_naturalItoIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:54:34.257216+00:00
-- url     : https://prove2.me/theorems/b668e40e-045d-4d45-a276-125eb2f59d6c
-- title:
--   Clark Ocone Family: is Brownian On Elementary iff ito Integral eq natural Ito Integral
-- statement:
--   Brownian compatibility on elementary adapted steps is equivalent to using the constructed
--   natural-filtration Itô integral.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ItoConsequences.lean#L426-L433
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ItoConsequences.lean#L426-L433

import Definitions.Def_Malliavin_ItoConstruction
import Definitions.Def_Malliavin_ItoConsequences
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

theorem Malliavin.ClarkOconeFamily.isBrownianOnElementary_iff_itoIntegral_eq_naturalItoIntegral
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓅) :
    C.IsBrownianOnElementary ↔
      C.itoIntegral = naturalItoIntegral C.isPreBrownian C.stronglyMeasurable
        C.naturalFiltration := by sorry
