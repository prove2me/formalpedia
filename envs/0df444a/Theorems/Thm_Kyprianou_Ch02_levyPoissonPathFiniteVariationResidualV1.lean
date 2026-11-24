-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyPoissonPathFiniteVariationResidualV1
-- name    : Kyprianou.Ch02.levyPoissonPathFiniteVariationResidualV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:32:58.02348+00:00
-- url     : https://prove2.me/theorems/aea59e34-d07d-4430-a506-70c82f6783e5
-- title:
--   Finite-first-moment Poisson path has linear residual after its actual signed jumps
-- statement:
--   For the explicit LeanLevy canonical path, finite first small-mark moment ensures locally absolute summability of the Poisson marks. Dominated convergence of the annulus series and compensators identifies the path as a deterministic linear drift plus the cumulative signed atomic series; its actual jumps equal the sums of all marks at the corresponding times. No assumption of distinct atom times is necessary.
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

theorem Kyprianou.Ch02.levyPoissonPathFiniteVariationResidualV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (K : ℕ → Ω → ℕ) (Z : ℕ → ℕ → Ω → ℝ × ℝ)
    (hd : IsPoissonPointFamily K Z ((volume : Measure ℝ).prod ν) P)
    (hν : IsLevyMeasure ν) (b : ℝ)
    (hfin : Integrable (fun x : ℝ => min (1 : ℝ) |x|) ν) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Summable (fun s : Set.Ioc (0 : ℝ≥0) T =>
        |levyJumpPath hd hν b s ω -
          leftLim (fun u : ℝ≥0 => levyJumpPath hd hν b u ω) s|) ∧
      levyJumpPath hd hν b T ω =
        (b - ∫ x in Set.Ioo (-1 : ℝ) 1, x ∂ν) * (T : ℝ) +
        ∑' s : Set.Ioc (0 : ℝ≥0) T,
          (levyJumpPath hd hν b s ω -
            leftLim (fun u : ℝ≥0 => levyJumpPath hd hν b u ω) s) := by
  sorry
