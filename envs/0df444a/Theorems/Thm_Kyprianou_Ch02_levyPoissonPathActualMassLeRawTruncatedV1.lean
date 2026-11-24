-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyPoissonPathActualMassLeRawTruncatedV1
-- name    : Kyprianou.Ch02.levyPoissonPathActualMassLeRawTruncatedV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T23:04:24.828257+00:00
-- url     : https://prove2.me/theorems/47c03ac2-52aa-42b3-8036-bf8d1d608d64
-- title:
--   Canonical pure-jump actual jump mass is bounded by raw truncated Poisson mass
-- statement:
--   For the canonical LeanLevy pure-jump path constructed from the specified Poisson point family, bound its actual positive-time small-jump mass on each integer horizon by the raw marked point mass. Under finite truncated first moment, use the almost sure finite nonnegative Poisson mass, finite large mark count, absolutely summable small marked points and the source compensated annulus limit. Continuous compensation drift contributes no jumps. The truncated absolute mark weight is subadditive, so simultaneous points do not invalidate the upper bound.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.12; LeanLevy path construction and generic Avram finite-cylinder path law.

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
open MeasureTheory ProbabilityTheory Complex Function Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.levyPoissonPathActualMassLeRawTruncatedV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (K : ℕ → Ω → ℕ) (Z : ℕ → ℕ → Ω → ℝ × ℝ)
    (hd : IsPoissonPointFamily K Z ((volume : Measure ℝ).prod ν) P)
    (hν : IsLevyMeasure ν) (b : ℝ)
    (hfinite : (∫⁻ x, ENNReal.ofReal (min (1 : ℝ) |x|) ∂ν) < ⊤) :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      (∑' s : Set.Ioc (0 : ℝ≥0) (n : ℝ≥0),
        ENNReal.ofReal
          (if |(levyJumpPath hd hν b) (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => (levyJumpPath hd hν b) u ω) (s : ℝ≥0)| ≤ (1 : ℝ)
           then |(levyJumpPath hd hν b) (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => (levyJumpPath hd hν b) u ω) (s : ℝ≥0)|
           else 0)) ≤
        (∫⁻ p : ℝ × ℝ,
      if 0 < p.1 ∧ p.1 ≤ (n : ℝ) then ENNReal.ofReal (min (1 : ℝ) |p.2|)
      else 0 ∂(poissonRandomMeasure K Z ω)) := by
  sorry
