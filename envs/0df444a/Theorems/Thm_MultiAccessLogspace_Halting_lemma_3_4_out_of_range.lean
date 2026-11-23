-- Prove2me | Theorems.Thm_MultiAccessLogspace_Halting_lemma_3_4_out_of_range
-- name    : MultiAccessLogspace.Halting.lemma_3_4_out_of_range
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:42:09.475086+00:00
-- url     : https://prove2.me/theorems/772aaca9-682d-449e-859e-d1d4cb81f9b4
-- title:
--   Lemma 3.4 — out-of-range probability
-- statement:
--   Let $X$ be a measurable random variable with values in $\mathbb N\cup\{\infty\}$ on a probability space $(\Omega,\mathcal F,P)$. Assume only that
--   $$
--   P(X=h)=2^{-h}\qquad(1\le h\le d).
--   $$
--   Then, with no further assumption on the remaining mass,
--   $$
--   P(X\notin[d])=2^{-d},\qquad [d]=\{1,\ldots,d\}.
--   $$
--   Indeed, the singleton events for $h=1,\ldots,d$ are pairwise disjoint, and their measures sum to $1-2^{-d}$. This is the first displayed calculation in the proof of Lemma 3.4 and supplies the $N2^{-d}$ term after a union bound over the coordinates. It includes $d=0$, when $[d]$ is empty and the complement has measure $1$.
--
--   **Formalization Note.** Values are represented by `ℕ∞`, so the event `X ∉ [d]` also includes `X = ∞`.
-- source:
--   William M. Hoza, STOC 2027 submission #92 (October 2026), Lemma 3.4 proof, first displayed equation, PDF p. 7 (printed p. 6); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/92.pdf; PDF SHA-256 92de35889559d87b5a77d83317b9c7b2c8924912fbd5c712f2af3c005c8998d8

import Mathlib
import Definitions.Def_MultiAccessLogspace_Halting_Rulers
import Definitions.Def_MultiAccessLogspace_Halting_HyporulerEvents

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MultiAccessLogspace.Halting

/-- The specified geometric masses on `[d]` force the complementary mass to be `2⁻ᵈ`. -/
theorem lemma_3_4_out_of_range {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (d : ℕ) (X : Ω → ℕ∞)
    (hmeas : Measurable X)
    (hmass : ∀ h : ℕ, 1 ≤ h → h ≤ d →
      P {ω | X ω = (h : ℕ∞)} = (2 : ℝ≥0∞)⁻¹ ^ h) :
    P {ω | ¬ InRangeENat d (X ω)} = (2 : ℝ≥0∞)⁻¹ ^ d := by sorry
