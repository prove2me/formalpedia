-- Prove2me | Theorems.Thm_Malliavin_tendsto_brownianLp_exhaustion
-- name    : Malliavin.tendsto_brownianLp_exhaustion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:20:56.780493+00:00
-- url     : https://prove2.me/theorems/f7cbad64-63e7-4bf7-8a97-16b47a061adf
-- title:
--   Malliavin: tendsto brownian Lp exhaustion
-- statement:
--   The Brownian classes converge in `L²` along the strict-past exhaustion `t - t/(n+2)`:
--   `‖B_t - B_{u n}‖² = t/(n+2) → 0`.  First brick of the left-continuity capstone.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L869-L908
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L869-L908

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_WienerChaos
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.ConditionalExpectation
import Definitions.Def_Malliavin_PointwiseCondExp
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
variable {B : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
variable {B : ℝ≥0 → W → ℝ}
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
  [SecondCountableTopology W] [IsGaussian P]

theorem Malliavin.tendsto_brownianLp_exhaustion (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    Filter.Tendsto (fun n : ℕ ↦ brownianLp hB (t - t / (n + 2))) Filter.atTop
      (nhds (brownianLp hB t)) := by sorry
