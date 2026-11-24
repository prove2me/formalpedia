-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyActualResidualLinearDriftAfterJumpsV1
-- name    : Kyprianou.Ch02.levyActualResidualLinearDriftAfterJumpsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T21:03:05.468988+00:00
-- url     : https://prove2.me/theorems/d6643ac9-e3e1-4328-9323-4708622dcdf2
-- title:
--   Zero-Gaussian original Levy process residual after its absolutely summable jumps is linear drift
-- statement:
--   For the exact original real Levy process with zero Gaussian coefficient and finite small-jump first moment, and an explicitly proved full-measure compact absolute-jump-summability event, show one deterministic real drift and one full-measure event such that at every time the original path equals linear drift plus the actual signed positive-time jump series. This isolates the genuinely stochastic continuous residual elimination, triplet uniqueness, and process-level path identity. No finite-variation conclusion is assumed; no one-time marginal law alone suffices.
-- source:
--   Kyprianou (2006) Chapter 2 Lemma 2.12, finite-variation form of the Lévy-Ito decomposition.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Function
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.levyActualResidualLinearDriftAfterJumpsV1
    (a : ℝ) (σ : ℝ≥0) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent
            ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ)) :
    (σ = 0 ∧ Integrable (fun x : ℝ => min (1 : ℝ) |x|) levyMeasure) →
    (∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Summable (fun s : Set.Ioc (0 : ℝ≥0) T =>
        |X (s : ℝ≥0) ω - leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)|)) →
    ∃ (drift : ℝ), ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      X T ω = drift * (T : ℝ) +
        ∑' s : Set.Ioc (0 : ℝ≥0) T,
          (X (s : ℝ≥0) ω - leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)) := by
  sorry
