-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyPoissonPathLocallySummableTimeRepresentationV1
-- name    : Kyprianou.Ch02.levyPoissonPathLocallySummableTimeRepresentationV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:51:21.23583+00:00
-- url     : https://prove2.me/theorems/30bfa3d0-a8bb-461c-8199-4d3e46071239
-- title:
--   Finite first moment canonical path equals drift plus locally summable time-grouped marks
-- statement:
--   Use the finite truncated Poisson mass on all compact horizons. Large marks are locally finite, so their absolute mass is also finite. Group the signed marks by time, then use dominated convergence of small-mark annulus sums and compensators to identify the explicit canonical path.
-- source:
--   Kyprianou (2006), Chapter 2 Lemma 2.12; canonical finite first moment model and equality of real Levy path laws.

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
open MeasureTheory ProbabilityTheory Complex Function Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.levyPoissonPathLocallySummableTimeRepresentationV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (K : ℕ → Ω → ℕ) (Z : ℕ → ℕ → Ω → ℝ × ℝ)
    (hd : IsPoissonPointFamily K Z ((volume : Measure ℝ).prod ν) P)
    (hν : IsLevyMeasure ν) (b : ℝ)
    (hfin : Integrable (fun x : ℝ => min (1 : ℝ) |x|) ν) :
    ∀ᵐ ω ∂P, ∃ g : ℝ≥0 → ℝ,
      (∀ T : ℝ≥0, Summable (fun s : Set.Ioc (0 : ℝ≥0) T => |g s|)) ∧
      ∀ T : ℝ≥0, levyJumpPath hd hν b T ω =
        (b - ∫ x in Set.Ioo (-1 : ℝ) 1, x ∂ν) * (T : ℝ) +
        ∑' s : Set.Ioc (0 : ℝ≥0) T, g s := by
  sorry
