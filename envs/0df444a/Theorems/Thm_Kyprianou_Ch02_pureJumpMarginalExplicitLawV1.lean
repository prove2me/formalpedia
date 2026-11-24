-- Prove2me | Theorems.Thm_Kyprianou_Ch02_pureJumpMarginalExplicitLawV1
-- name    : Kyprianou.Ch02.pureJumpMarginalExplicitLawV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:18:49.724373+00:00
-- url     : https://prove2.me/theorems/27dcef22-7398-4f91-bfa8-cad2e73a5fef
-- title:
--   Existence of the pure-jump time-one marginal with explicit exponent
-- statement:
--   Take the time-one marginal of the proved zero-Gaussian Lévy process constructor, explicitly unfolding the characteristic exponent. The statement avoids duplicate exponent definitions.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.14, via the Lévy–Khintchine small-time extraction and uniqueness.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_LeanLevy_Levy_CompensatedIntegral
open MeasureTheory ProbabilityTheory Complex Filter Topology Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.pureJumpMarginalExplicitLawV1
    (T : ProbabilityTheory.LevyKhintchineTriple) :
    ∃ (R : Measure ℝ), IsProbabilityMeasure R ∧
      ∀ ξ : ℝ, charFun R ξ = Complex.exp
        (Complex.I * ((T.drift * ξ : ℝ) : ℂ) +
          ∫ y, ProbabilityTheory.levyCompensatedIntegrand ξ y ∂T.levyMeasure) := by
  sorry
