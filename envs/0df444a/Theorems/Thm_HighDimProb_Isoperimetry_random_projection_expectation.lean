-- Prove2me | Theorems.Thm_HighDimProb_Isoperimetry_random_projection_expectation
-- name    : HighDimProb.Isoperimetry.random_projection_expectation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T05:41:00.513467+00:00
-- url     : https://prove2.me/theorems/125e23cf-1a83-4b84-8061-6e0c2472644b
-- title:
--   Lemma 5.3.2(a) — Random projection, expectation
-- statement:
--   This is **Lemma 5.3.2(a)**: the expected squared norm of a fixed vector's random projection,
--   exactly, with no approximation — the first of the two direct inputs to the
--   Johnson-Lindenstrauss Lemma's proof.
--
--   Let $(\Omega, \mathcal F, \mathrm{Prob})$ be a probability space, $n, m \in \mathbb N$, and
--   let $P : \Omega \to (\mathbb R^n \to \mathbb R^n)$ be a random orthogonal projection of rank
--   $m$ uniformly distributed in the Grassmannian $G_{n,m}$ (the companion definition
--   `IsUniformProjection`). For any fixed point $z \in \mathbb R^n$,
--
--   $$
--   \bigl(\mathbb E \, \|P_\omega z\|_2^2\bigr)^{1/2} \;=\; \sqrt{\frac{m}{n}}\,\|z\|_2 .
--   $$
--
--   This says a random $m$-dimensional projection shrinks the norm of any fixed vector by
--   exactly the factor $\sqrt{m/n}$ *on average* — the scaling that makes the rescaled
--   projection $Q = \sqrt{n/m}\,P$ of Theorem 5.3.1 an isometry in expectation. Part (b) of the
--   same lemma upgrades this expectation identity to a high-probability concentration bound.
--
--   **Formalization Note** The expectation is the Bochner integral $\int_\Omega \|P_\omega
--   z\|^2 \, d\mathrm{Prob}$; per Mathlib's convention this equals $0$ if the integrand is not
--   integrable, which does not affect the claim since $\|P_\omega z\|^2 \le \|z\|^2$ is bounded
--   and hence always integrable under a probability measure. No constant is existentially
--   quantified here, since the book proves this part as an exact identity.
-- source:
--   Vershynin, High-Dimensional Probability (2018), Lemma 5.3.2(a), p. 118 (PDF p. 126)

import Mathlib
import Definitions.Def_HighDimProb_Isoperimetry_UniformProjection

open MeasureTheory

namespace HighDimProb.Isoperimetry

/-- **Lemma 5.3.2(a)** (Random projection, expectation), Vershynin, *High-Dimensional
Probability* (2018), p. 118.

Let `P` be a projection in `ℝⁿ` onto a random `m`-dimensional subspace uniformly distributed
in `G_{n,m}`. Let `z ∈ ℝⁿ` be a fixed point. Then

`(E ‖Pz‖₂²)^{1/2} = √(m/n) ‖z‖₂`. -/
theorem random_projection_expectation
    {Ω : Type} [MeasurableSpace Ω] (Prob : Measure Ω) [IsProbabilityMeasure Prob]
    {n : ℕ} (m : ℕ) (P : Ω → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hP : IsUniformProjection Prob m P) (z : EuclideanSpace ℝ (Fin n)) :
    Real.sqrt (∫ ω, ‖P ω z‖ ^ 2 ∂Prob) = Real.sqrt ((m : ℝ) / (n : ℝ)) * ‖z‖ := by sorry

end HighDimProb.Isoperimetry
