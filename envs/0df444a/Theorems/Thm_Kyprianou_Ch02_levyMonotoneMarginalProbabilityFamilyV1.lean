-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyMonotoneMarginalProbabilityFamilyV1
-- name    : Kyprianou.Ch02.levyMonotoneMarginalProbabilityFamilyV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:47:31.187889+00:00
-- url     : https://prove2.me/theorems/279dfb07-5671-44f5-be92-16db552bcb04
-- title:
--   Actual monotone Lévy marginal probability family and nonnegative support
-- statement:
--   Use the prescribed triplet exponent, its proved continuity and value at zero, and the actual positive-time laws of X. Stationarity and start_zero imply a.e. measurable marginals; monotone paths give each law zero negative mass.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.14, via the Lévy–Khintchine small-time extraction and uniqueness.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false
open Filter Topology Set

theorem Kyprianou.Ch02.levyMonotoneMarginalProbabilityFamilyV1
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
            ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ))
    (hm : ∀ᵐ ω ∂P, Monotone (fun t : ℝ≥0 => X t ω)) :
    ∃ M : {t : ℝ // 0 < t} → ProbabilityMeasure ℝ,
      (∀ t ξ, charFun (M t : Measure ℝ) ξ =
        Complex.exp (((t.val : ℝ) : ℂ) *
          Kyprianou.Ch01.levyTripleExponent
            ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ)) ∧
      ∀ t, (M t : Measure ℝ) (Set.Iio (0 : ℝ)) = 0 := by
  sorry
