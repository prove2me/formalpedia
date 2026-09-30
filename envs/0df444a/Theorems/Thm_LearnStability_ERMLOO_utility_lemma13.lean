-- Prove2me | Theorems.Thm_LearnStability_ERMLOO_utility_lemma13
-- name    : LearnStability.ERMLOO.utility_lemma13
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T18:21:15.591382+00:00
-- url     : https://prove2.me/theorems/2667e8bf-7b60-4b6f-afa9-2c840a26887a
-- title:
--   Utility Lemma 13 — if X ≤ Y a.s. then E|X| ≤ |E X| + 2 E|Y|
-- statement:
--   Let $X$ and $Y$ be integrable real random variables on a probability space such that $X\le Y$ almost surely. Then
--   $$\mathbb E\big[|X|\big]\le\big|\mathbb E[X]\big|+2\,\mathbb E\big[|Y|\big].$$
--
--   The inequality turns a bound on a signed expectation, together with a one-sided pointwise majorant, into a bound on an expected absolute value; it is the step from on-average generalization to generalization in Lemma 14.
--
--   **Formalization Note.** Integrability of $X$ and $Y$ is assumed (the paper leaves it implicit); without it Lean's integrals default to $0$.
-- source:
--   Shalev-Shwartz, Shamir, Srebro and Sridharan, Learnability, Stability and Uniform Convergence, JMLR 11 (2010), p. 2650, Utility Lemma 13

import Mathlib

open MeasureTheory

namespace LearnStability.ERMLOO

theorem utility_lemma13 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ) (hX : Integrable X μ) (hY : Integrable Y μ) (hXY : X ≤ᵐ[μ] Y) :
    ∫ ω, |X ω| ∂μ ≤ |∫ ω, X ω ∂μ| + 2 * ∫ ω, |Y ω| ∂μ := by sorry

end LearnStability.ERMLOO
