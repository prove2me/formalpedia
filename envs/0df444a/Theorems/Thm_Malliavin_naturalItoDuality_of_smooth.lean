-- Prove2me | Theorems.Thm_Malliavin_naturalItoDuality_of_smooth
-- name    : Malliavin.naturalItoDuality_of_smooth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:44:39.281827+00:00
-- url     : https://prove2.me/theorems/e86d3c3e-f761-4abb-99d0-7ac8f4e1ff27
-- title:
--   Malliavin: natural Ito Duality of smooth
-- statement:
--   Duality on the smooth core extends to every member of `D12` by graph closure.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalClarkOcone.lean#L483-L544
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalClarkOcone.lean#L483-L544

import Definitions.Def_Malliavin_KernelIdentification
import Definitions.Def_Malliavin_NaturalClarkOcone
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

theorem Malliavin.naturalItoDuality_of_smooth
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (hCore : SmoothNaturalItoDuality
      hB coordinate coordinate_apply generated hsm hnat)
    (F : D12 P) (U : PredictableProcessL2 𝓅 P) :
    inner ℝ (F.1 - expectationL2 F.1) (naturalItoIntegral hB hsm hnat U) =
      inner ℝ
        (predictableProjection 𝓅
          (Malliavin.timeDerivative hB coordinate coordinate_apply generated
            (mderivD12 P F))) U := by sorry
