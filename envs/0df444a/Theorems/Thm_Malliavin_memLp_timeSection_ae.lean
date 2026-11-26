-- Prove2me | Theorems.Thm_Malliavin_memLp_timeSection_ae
-- name    : Malliavin.memLp_timeSection_ae
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:12:09.316873+00:00
-- url     : https://prove2.me/theorems/3ac183b7-6ab8-46bd-a99e-9d2618cea76a
-- title:
--   Malliavin: mem Lp time Section ae
-- statement:
--   A product-`L²` representative has an `L²(P)` time section for almost every time.
--   The exceptional null set may depend on the representative, so this does not define evaluation
--   of a product-`L²` class at any prescribed time.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOcone.lean#L59-L64
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOcone.lean#L59-L64

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

theorem Malliavin.memLp_timeSection_ae (U : TimeProcessL2 P) :
    ∀ᵐ t ∂nonnegativeLebesgueMeasure, MemLp (fun ω ↦ U (t, ω)) 2 P := by sorry
