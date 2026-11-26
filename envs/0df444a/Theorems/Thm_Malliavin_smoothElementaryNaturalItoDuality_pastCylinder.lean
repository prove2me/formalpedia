-- Prove2me | Theorems.Thm_Malliavin_smoothElementaryNaturalItoDuality_pastCylinder
-- name    : Malliavin.smoothElementaryNaturalItoDuality_pastCylinder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:46:33.297801+00:00
-- url     : https://prove2.me/theorems/9f2fdc09-5a18-4fea-86b9-4f9f77c84d3b
-- title:
--   Malliavin: smooth Elementary Natural Ito Duality past Cylinder
-- statement:
--   Malliavin--Itô duality against an elementary predictable process whose coefficient is a
--   smooth bounded cylinder in Brownian coordinates from the past.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalClarkOcone.lean#L146-L317
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalClarkOcone.lean#L146-L317

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

theorem Malliavin.smoothElementaryNaturalItoDuality_pastCylinder
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (G : W → ℝ) (hG : IsSmoothBounded G)
    {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (hb : ∃ C, ∀ y, |f y| ≤ C)
    (hb' : ∃ C, ∀ y, ‖fderiv ℝ f y‖ ≤ C)
    (t : Fin n → ℝ≥0) (a b : ℝ≥0) (hab : a ≤ b)
    (ht : ∀ i, t i ≤ a) :
    let Z := pastCylinderLpMeas hB coordinate coordinate_apply hsm hnat
      f hf hb hb' t a ht
    inner ℝ (hG.toLp P - expectationL2 (hG.toLp P))
        (elementaryBrownianValue hB hsm hnat hab Z) =
      inner ℝ
        (predictableProjection 𝓅
          (Malliavin.timeDerivative hB coordinate coordinate_apply generated
            (hG.mderivLp P)))
        (elementaryPredictable 𝓅 a b Z) := by sorry
