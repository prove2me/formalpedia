-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m87_qpos_interval_from_halfline_bridge
-- name    : Kyprianou.Ch08.StageB.p2m87_qpos_interval_from_halfline_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:39:32.46282+00:00
-- url     : https://prove2.me/theorems/dd94395e-5a1b-4371-8a44-53bb6ca85201
-- title:
--   Positive-discount interval occupation from the two half-line identities
-- statement:
--   Given the exact positive-discount killed half-line occupation identities at starting levels x and a, split the half-line occupation from x at the upper passage. Strong Markov at tauPlus a, absence of positive jumps, and the proved Theorem 8.1 exit ratio W(q,x)/W(q,a) give the discounted occupation subtraction. Cancelling the common exponential scale term yields the exact killed interval density on measurable sets.
-- source:
--   Kyprianou (2006), proof of Theorem 8.7, upper-barrier strong Markov subtraction and equations (8.20), (8.28); bridge from Chapter 8 source results 8.1 and 8.8.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

/-- Source-faithful bridge: upper-barrier strong Markov subtraction from the half-line resolvent identities. -/
theorem p2m87_qpos_interval_from_halfline_bridge :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ (q a x : ℝ), 0 < q → 0 < a → 0 ≤ x → x ≤ a →
      ∀ (A : Set ℝ), MeasurableSet A →
        ((volume.restrict (Set.Ici (0 : ℝ))).withDensity
          (fun y : ℝ => ENNReal.ofReal
            (killedHalflineDensity ψ q (W q) x y))) A =
        ∫⁻ t : ℝ≥0,
          ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
            P {ω | (t : WithTop ℝ≥0) <
              tauMinus (shifted D.X x) 0 ω ∧
              shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue →
        ((volume.restrict (Set.Ici (0 : ℝ))).withDensity
          (fun y : ℝ => ENNReal.ofReal
            (killedHalflineDensity ψ q (W q) a y))) A =
        ∫⁻ t : ℝ≥0,
          ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
            P {ω | (t : WithTop ℝ≥0) <
              tauMinus (shifted D.X a) 0 ω ∧
              shifted D.X a t ω ∈ A} ∂positiveTimeLebesgue →
        ((volume.restrict (Set.Icc 0 a)).withDensity
          (fun y : ℝ => ENNReal.ofReal
            (killedIntervalDensity (W q) a x y))) A =
        ∫⁻ t : ℝ≥0,
          ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
            P {ω | (t : WithTop ℝ≥0) <
              min (tauMinus (shifted D.X x) 0 ω)
                (tauPlus (shifted D.X x) a ω) ∧
              shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue := by
  sorry

end Kyprianou.Ch08.StageB
