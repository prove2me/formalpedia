-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianChaosTotal_iff_dense_orderedChainSpan
-- name    : Malliavin.BrownianIteratedConstruction.brownianChaosTotal_iff_dense_orderedChainSpan
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:58:59.144809+00:00
-- url     : https://prove2.me/theorems/77800e96-d2bc-5a4b-acbb-f026ba2fd894
-- title:
--   Brownian Iterated Construction: brownian Chaos Total iff dense ordered Chain Span
-- statement:
--   Canonical Brownian-chaos totality is equivalent to density of finite ordered increment
--   products.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianChaosTotality.lean#L146-L150
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianChaosTotality.lean#L146-L150

import Definitions.Def_Malliavin_BrownianChaosMartingaleRepresentation
import Definitions.Def_Malliavin_BrownianChaosTotality
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin Malliavin.BrownianIteratedConstruction
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [CompleteSpace W] [BorelSpace W]

theorem Malliavin.BrownianIteratedConstruction.brownianChaosTotal_iff_dense_orderedChainSpan
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t)) :
    BrownianChaosTotal hB ↔ Dense (brownianOrderedChainSpan hB : Set (RandomL2 P)) := by sorry
