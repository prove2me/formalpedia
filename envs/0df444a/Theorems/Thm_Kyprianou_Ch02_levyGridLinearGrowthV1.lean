-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyGridLinearGrowthV1
-- name    : Kyprianou.Ch02.levyGridLinearGrowthV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:52:02.329646+00:00
-- url     : https://prove2.me/theorems/08353024-6dd9-4735-b295-a76132627f61
-- title:
--   Exponential grid lower bound implies linear growth of the real exponent
-- statement:
--   The positive uniform lower bound on powers of the exponential absolute-increment expectation bounds n times the increment loss. The pointwise inequality 1-cos(ξx) ≤ C(1+|ξ|)(1-exp(-|x|)) and the derivative of the characteristic exponential at zero yield the asserted growth bound.
-- source:
--   Kyprianou (2006), Lemma 2.12

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.levyGridLinearGrowthV1
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
    (∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ,
        c ≤ (∫ ω, Real.exp (-|X (((n : ℝ≥0) + 1)⁻¹) ω|) ∂P) ^ (n + 1)) →
    ∃ K : ℝ, ∀ ξ : ℝ,
      -(Kyprianou.Ch01.levyTripleExponent ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ).re ≤ K * (1 + |ξ|) := by sorry
