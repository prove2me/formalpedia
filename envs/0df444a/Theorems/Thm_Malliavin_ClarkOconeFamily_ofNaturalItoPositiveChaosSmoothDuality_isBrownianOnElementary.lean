-- Prove2me | Theorems.Thm_Malliavin_ClarkOconeFamily_ofNaturalItoPositiveChaosSmoothDuality_isBrownianOnElementary
-- name    : Malliavin.ClarkOconeFamily.ofNaturalItoPositiveChaosSmoothDuality_isBrownianOnElementary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:55:02.487808+00:00
-- url     : https://prove2.me/theorems/44b49a0d-e03b-4725-b622-ee25c430a48b
-- title:
--   Clark Ocone Family: of Natural Ito Positive Chaos Smooth Duality is Brownian On Elementary
-- statement:
--   The chaos/smooth-core constructor uses the genuine Brownian integral on every elementary
--   adapted process.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ChaosMartingaleRepresentation.lean#L184-L200
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ChaosMartingaleRepresentation.lean#L184-L200

import Definitions.Def_Malliavin_NaturalClarkOcone
import Definitions.Def_Malliavin_WienerChaos
import Definitions.Def_Malliavin_ChaosMartingaleRepresentation
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

theorem Malliavin.ClarkOconeFamily.ofNaturalItoPositiveChaosSmoothDuality_isBrownianOnElementary
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (hpositive : ∀ n : ℕ, 0 < n →
      (homogeneousChaos hB n : Submodule ℝ (RandomL2 P)) ≤
        naturalItoRange hB hsm hnat)
    (hDuality : SmoothNaturalItoDuality
      hB coordinate coordinate_apply generated hsm hnat) :
    (ClarkOconeFamily.ofNaturalItoPositiveChaosSmoothDuality
      hB coordinate coordinate_apply generated hsm hnat hpositive hDuality
      ).IsBrownianOnElementary := by sorry
