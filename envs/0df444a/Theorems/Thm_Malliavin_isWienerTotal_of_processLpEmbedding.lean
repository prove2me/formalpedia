-- Prove2me | Theorems.Thm_Malliavin_isWienerTotal_of_processLpEmbedding
-- name    : Malliavin.isWienerTotal_of_processLpEmbedding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:09:18.268795+00:00
-- url     : https://prove2.me/theorems/41d4669f-a85c-4dd4-9556-63b555bcd48f
-- title:
--   Malliavin: is Wiener Total of process Lp Embedding
-- statement:
--   Totality of the selected homogeneous ranges under the exact `L²` exhaustion condition used
--   by the tower.
--
--   Surjectivity of `processLpEmbedding` makes the positive-order tower take its Hilbert-equivalence
--   branch onto the centered subspace.  Each summand is represented by a selected multiple operator,
--   and order zero supplies the constant part.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerChaos.lean#L371-L428
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerChaos.lean#L371-L428

import Definitions.Def_Malliavin_MultipleIntegral
import Definitions.Def_Malliavin_WienerChaos
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Topology symmDiff
noncomputable section
open Malliavin
universe u v u_1 u_2 u_4 u_6
universe u₁ u₂ u₃
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.isWienerTotal_of_processLpEmbedding
    (hB : IsPreBrownianReal B P) [SecondCountableTopology (RandomL2 P)]
    (hmeas : ∀ t, Measurable (B t))
    (hexhausts : Function.Surjective (processLpEmbedding P B hmeas)) :
    IsWienerTotal hB := by sorry
