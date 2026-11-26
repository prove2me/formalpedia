-- Prove2me | Theorems.Thm_Malliavin_ClarkOconeFamily_ofNaturalIto_isBrownianOnElementary
-- name    : Malliavin.ClarkOconeFamily.ofNaturalIto_isBrownianOnElementary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:53:36.521789+00:00
-- url     : https://prove2.me/theorems/40a26656-29f5-4e62-bdfa-9124f8f72040
-- title:
--   Clark Ocone Family: of Natural Ito is Brownian On Elementary
-- statement:
--   A family built by `ofNaturalIto` automatically satisfies the textbook elementary formula
--   `∫_a^b Z dB = Z (B_b - B_a)`. Martingale representation and duality are irrelevant to this
--   compatibility; they are present only because `ofNaturalIto` produces a full family.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ItoConsequences.lean#L438-L463
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ItoConsequences.lean#L438-L463

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

theorem Malliavin.ClarkOconeFamily.ofNaturalIto_isBrownianOnElementary
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (hMRT : ∀ G : RandomL2 P, ∃ U : PredictableProcessL2 𝓅 P,
      G = expectationL2 G + naturalItoIntegral hB hsm hnat U)
    (hDuality : ∀ (F : D12 P) (U : PredictableProcessL2 𝓅 P),
      inner ℝ (F.1 - expectationL2 F.1)
          (naturalItoIntegral hB hsm hnat U) =
        inner ℝ (predictableProjection 𝓅
          (Malliavin.timeDerivative hB coordinate coordinate_apply generated
            (mderivD12 P F))) U) :
    (ClarkOconeFamily.ofNaturalIto (W := W) (P := P) (B := B)
      hB coordinate coordinate_apply generated hsm hnat
      hMRT hDuality).IsBrownianOnElementary := by sorry
