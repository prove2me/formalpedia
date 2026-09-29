-- Prove2me | Theorems.Thm_HighDimProb_Isoperimetry_random_projection_concentration
-- name    : HighDimProb.Isoperimetry.random_projection_concentration
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T05:41:36.923068+00:00
-- url     : https://prove2.me/theorems/0b94c6f2-1ac6-4671-8717-5a6ccb5e183c
-- title:
--   Lemma 5.3.2(b) — Random projection, concentration
-- statement:
--   This is **Lemma 5.3.2(b)**: a fixed vector's random projection concentrates, with
--   sub-gaussian-type failure probability, around the value Lemma 5.3.2(a) computes in
--   expectation — the second, and final, direct input to the Johnson-Lindenstrauss Lemma's
--   proof, via Theorem 5.1.4.
--
--   There is an absolute constant $c > 0$ such that the following holds. Let
--   $(\Omega, \mathcal F, \mathrm{Prob})$ be a probability space, $n, m \in \mathbb N$, and let
--   $P : \Omega \to (\mathbb R^n \to \mathbb R^n)$ be a random orthogonal projection of rank $m$
--   uniformly distributed in the Grassmannian $G_{n,m}$ (the companion definition
--   `IsUniformProjection`). For any fixed point $z \in \mathbb R^n$ and any $\varepsilon \in
--   \mathbb R$,
--
--   $$
--   \mathrm{Prob}\left\{(1-\varepsilon)\sqrt{\tfrac mn}\,\|z\|_2 \;\le\; \|P_\omega z\|_2 \;\le\;
--     (1+\varepsilon)\sqrt{\tfrac mn}\,\|z\|_2\right\} \;\ge\; 1 - 2\exp(-c\varepsilon^2 m).
--   $$
--
--   Together with Theorem 5.1.4 (applied to the Lipschitz function $x \mapsto \|P_\omega x\|_2$
--   restricted to the sphere), this shows the norm of a fixed vector's random projection is
--   tightly concentrated around its expected value from part (a), for every individual vector
--   $z$; the Johnson-Lindenstrauss Lemma is obtained by a union bound of this single-vector
--   statement over all $N^2$ pairwise differences of the data set $X$.
--
--   **Formalization Note** Same absolute-constant discipline as the goal theorem: $c$ is
--   existentially quantified ahead of every other object, so no numeral is fixed for it. The
--   book's hypothesis $\varepsilon > 0$ is imposed explicitly as `hε`, matching the book's own
--   statement exactly.
-- source:
--   Vershynin, High-Dimensional Probability (2018), Lemma 5.3.2(b), p. 118 (PDF p. 126)

import Mathlib
import Definitions.Def_HighDimProb_Isoperimetry_UniformProjection

open MeasureTheory

namespace HighDimProb.Isoperimetry

/-- **Lemma 5.3.2(b)** (Random projection, concentration), Vershynin, *High-Dimensional
Probability* (2018), p. 118.

Let `P` be a projection in `ℝⁿ` onto a random `m`-dimensional subspace uniformly distributed
in `G_{n,m}`. Let `z ∈ ℝⁿ` be a fixed point and `ε > 0`. Then, with probability at least
`1 − 2exp(−cε²m)`,

`(1 − ε) √(m/n) ‖z‖₂ ≤ ‖Pz‖₂ ≤ (1 + ε) √(m/n) ‖z‖₂`. -/
theorem random_projection_concentration :
    ∃ c : ℝ, 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (Prob : Measure Ω) [IsProbabilityMeasure Prob]
        {n : ℕ} (m : ℕ) (P : Ω → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
        (hP : IsUniformProjection Prob m P) (z : EuclideanSpace ℝ (Fin n)) {ε : ℝ} (hε : 0 < ε),
        1 - 2 * Real.exp (-(c * ε ^ 2 * (m : ℝ))) ≤
          Prob.real {ω | (1 - ε) * Real.sqrt ((m : ℝ) / (n : ℝ)) * ‖z‖ ≤ ‖P ω z‖ ∧
            ‖P ω z‖ ≤ (1 + ε) * Real.sqrt ((m : ℝ) / (n : ℝ)) * ‖z‖} := by sorry

end HighDimProb.Isoperimetry
