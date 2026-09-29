-- Prove2me | Theorems.Thm_HighDimProb_Isoperimetry_johnson_lindenstrauss
-- name    : HighDimProb.Isoperimetry.johnson_lindenstrauss
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T05:42:11.32549+00:00
-- url     : https://prove2.me/theorems/c223b02f-3391-4137-a55f-6139d5332951
-- title:
--   Theorem 5.3.1 — Johnson-Lindenstrauss Lemma
-- statement:
--   This is the **Johnson-Lindenstrauss Lemma** (Theorem 5.3.1), the goal theorem of this
--   mission: any $N$ points in a Euclidean space of arbitrarily high dimension $n$ can be
--   projected, by a single random linear map that does not depend on the data, into a space of
--   dimension only $O(\log N)$ while distorting every pairwise distance by at most a factor of
--   $1 \pm \varepsilon$.
--
--   There are absolute constants $C, c > 0$ such that the following holds. Let $n, m \in
--   \mathbb N$, let $X$ be a finite set of points in $\mathbb R^n$, and let $\varepsilon > 0$
--   with
--
--   $$
--   m \;\ge\; \frac{C}{\varepsilon^2}\,\log |X| .
--   $$
--
--   Let $(\Omega, \mathcal F, \mathrm{Prob})$ be a probability space and $P : \Omega \to
--   (\mathbb R^n \to \mathbb R^n)$ a random orthogonal projection of rank $m$, uniformly
--   distributed in the Grassmannian $G_{n,m}$ (the companion definition `IsUniformProjection`).
--   Then
--
--   $$
--   \mathrm{Prob}\Bigl\{\forall x, y \in X : (1-\varepsilon)\|x-y\|_2 \le
--     \bigl\|\sqrt{\tfrac nm}\,P_\omega(x-y)\bigr\|_2 \le (1+\varepsilon)\|x-y\|_2\Bigr\}
--     \;\ge\; 1 - 2\exp(-c\varepsilon^2 m).
--   $$
--
--   That is, with the stated probability, the scaled projection $Q_\omega := \sqrt{n/m}\,P_\omega$
--   is *simultaneously*, for every pair of points $x, y \in X$, a $(1\pm\varepsilon)$-approximate
--   isometry.
--
--   Two features make this remarkable: the map $Q$ is **non-adaptive** — a single random object
--   drawn without looking at the data $X$ works for the whole set with high probability — and
--   the ambient dimension $n$ plays no role in the bound, only the target dimension $m$, the
--   number of points $N = |X|$, and $\varepsilon$.
--
--   **Formalization Note** $X$ is a `Finset` of points, matching the book's "$N$ points"; the
--   conclusion quantifies universally over *all* pairs $x, y \in X$ *inside* the same
--   probability event — not one high-probability event per pair — which is exactly the union-
--   bound content that makes this a genuine dimension-reduction statement for a whole point set
--   rather than a restatement of Lemma 5.3.2(b) for one fixed difference vector. Both $C$ and
--   $c$ are existentially quantified ahead of every other object (the probability space, $n$,
--   $m$, $X$, $\varepsilon$, and $P$), so neither numeral is fixed; the book's proof gives
--   $c = c_0/2$ for the $c_0$ of Lemma 5.3.2(b) under the stated hypothesis on $m$, but only the
--   existence of *some* absolute $c$ is asserted here, matching the book's own statement.
-- source:
--   Vershynin, High-Dimensional Probability (2018), Theorem 5.3.1, p. 118 (PDF p. 126)

import Mathlib
import Definitions.Def_HighDimProb_Isoperimetry_UniformProjection

open MeasureTheory

namespace HighDimProb.Isoperimetry

/-- **Theorem 5.3.1** (Johnson-Lindenstrauss Lemma), Vershynin, *High-Dimensional Probability*
(2018), p. 118.

Let `X` be a set of `N` points in `ℝⁿ` and `ε > 0`. Assume that `m ≥ (C/ε²) log N`. Consider a
random `m`-dimensional subspace `E` in `ℝⁿ` uniformly distributed in `G_{n,m}`. Denote the
orthogonal projection onto `E` by `P`. Then, with probability at least `1 − 2exp(−cε²m)`, the
scaled projection `Q := √(n/m) P` is an approximate isometry on `X`:

`(1 − ε) ‖x − y‖₂ ≤ ‖Qx − Qy‖₂ ≤ (1 + ε) ‖x − y‖₂` for all `x, y ∈ X`. -/
theorem johnson_lindenstrauss :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (Prob : Measure Ω) [IsProbabilityMeasure Prob]
        {n : ℕ} (m : ℕ) (X : Finset (EuclideanSpace ℝ (Fin n))) {ε : ℝ} (hε : 0 < ε),
        (m : ℝ) ≥ (C / ε ^ 2) * Real.log (X.card : ℝ) →
        ∀ (P : Ω → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))),
        IsUniformProjection Prob m P →
        1 - 2 * Real.exp (-(c * ε ^ 2 * (m : ℝ))) ≤
          Prob.real {ω | ∀ x ∈ X, ∀ y ∈ X,
            (1 - ε) * ‖x - y‖ ≤ ‖Real.sqrt ((n : ℝ) / (m : ℝ)) • P ω (x - y)‖ ∧
            ‖Real.sqrt ((n : ℝ) / (m : ℝ)) • P ω (x - y)‖ ≤ (1 + ε) * ‖x - y‖} := by sorry

end HighDimProb.Isoperimetry
