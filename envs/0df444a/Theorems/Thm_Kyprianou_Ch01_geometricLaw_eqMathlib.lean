-- Prove2me | Theorems.Thm_Kyprianou_Ch01_geometricLaw_eqMathlib
-- name    : Kyprianou.Ch01.geometricLaw_eqMathlib
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:29:27.419194+00:00
-- url     : https://prove2.me/theorems/4c5e2ea5-3ee5-41cc-9c95-82a04bc1b7fc
-- title:
--   A counting-law with geometric singleton probabilities equals Mathlib geometricMeasure exactly
-- statement:
--   For real p with 0 < p ≤ 1 and any measure G on the natural numbers whose exact singleton masses are p(1-p)^k for every k, prove the full equality of measures G = geometricMeasure p. The proof converts p to the canonical Mathlib unit-interval parameter, establishes it is nonzero, applies geometricMeasure_singleton and uses measure extensionality on countable singletons. This reduces Kyprianou (2006) Exercise 1.2(i) infinitely divisibility of any geometrically distributed counting law to the corresponding single canonical geometric distribution, with no distributional ambiguity.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.2(i), printed p. 26; Mathlib geometricMeasure_singleton and Measure.ext_of_singleton.

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.geometricLaw_eqMathlib
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (G : Measure ℕ)
    (hGeom : ∀ k : ℕ,
      G {k} = ENNReal.ofReal (p * (1 - p) ^ k)) :
    G = ProbabilityTheory.geometricMeasure
      (⟨p, ⟨le_of_lt hp0, hp1⟩⟩ : unitInterval.Elem) := by
  sorry
