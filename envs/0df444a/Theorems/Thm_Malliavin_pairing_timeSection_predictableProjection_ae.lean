-- Prove2me | Theorems.Thm_Malliavin_pairing_timeSection_predictableProjection_ae
-- name    : Malliavin.pairing_timeSection_predictableProjection_ae
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:27:13.479463+00:00
-- url     : https://prove2.me/theorems/4889bde3-6b3d-5f36-bbbf-2b5372d4ee6a
-- title:
--   Malliavin: pairing time Section predictable Projection ae
-- statement:
--   **Uniform conditional moments against a fixed coefficient**: for `Z ∈ L²` measurable for
--   `𝓕 a`, the sectionwise pairings of the correction `Π U - U` with `Z` vanish for almost every
--   `t > a`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L436-L497
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L436-L497

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
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›)
omit [CompleteSpace W] [BorelSpace W]

theorem Malliavin.pairing_timeSection_predictableProjection_ae (U : TimeProcessL2 P) (a : ℝ≥0)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    ∀ᵐ t ∂nonnegativeLebesgueMeasure, a < t →
      ∫ ω, ((predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) (t, ω) - U (t, ω))
        * (Z : Lp ℝ 2 P) ω ∂P = 0 := by sorry
