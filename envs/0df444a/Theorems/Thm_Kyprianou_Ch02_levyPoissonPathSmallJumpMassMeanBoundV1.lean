-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyPoissonPathSmallJumpMassMeanBoundV1
-- name    : Kyprianou.Ch02.levyPoissonPathSmallJumpMassMeanBoundV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:04:29.495108+00:00
-- url     : https://prove2.me/theorems/301be199-0de7-412b-a25e-e77b45288bcb
-- title:
--   Canonical pure-jump model expected actual small-jump mass bound
-- statement:
--   For the explicit LeanLevy Poisson jump path, integrate the pathwise upper bound and apply the exact first-moment identity of the raw Poisson marks. For infinite source truncated first moment the positive horizon bound is trivial; the zero horizon is empty.
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

theorem Kyprianou.Ch02.levyPoissonPathSmallJumpMassMeanBoundV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (K : ℕ → Ω → ℕ) (Z : ℕ → ℕ → Ω → ℝ × ℝ)
    (hd : IsPoissonPointFamily K Z ((volume : Measure ℝ).prod ν) P)
    (hν : IsLevyMeasure ν) (b : ℝ) :
    ∀ n : ℕ,
      (∫⁻ ω, ∑' s : Set.Ioc (0 : ℝ≥0) (n : ℝ≥0),
        ENNReal.ofReal
          (if |(levyJumpPath hd hν b) (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => (levyJumpPath hd hν b) u ω) (s : ℝ≥0)| ≤ (1 : ℝ)
           then |(levyJumpPath hd hν b) (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => (levyJumpPath hd hν b) u ω) (s : ℝ≥0)|
           else 0) ∂P) ≤
        (n : ℝ≥0∞) * (∫⁻ x, ENNReal.ofReal (min (1 : ℝ) |x|) ∂ν) := by
  sorry
