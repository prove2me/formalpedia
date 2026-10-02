-- Prove2me | Theorems.Thm_HighDimProb_RandomVectors_grothendieck_identity
-- name    : HighDimProb.RandomVectors.grothendieck_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T06:43:57.008431+00:00
-- url     : https://prove2.me/theorems/2e2d6d44-44a2-4d38-9a40-b187964450b5
-- title:
--   Lemma 3.6.6 — Grothendieck's identity
-- statement:
--   This is **Grothendieck's identity** (Lemma 3.6.6), an elementary but pivotal fact
--   translating the geometry of two unit vectors into the correlation of the *signs* of their
--   Gaussian projections — the key identity behind the Goemans-Williamson randomized rounding
--   that both the maximum-cut approximation algorithm (Theorem 3.6.5) and the sharper
--   $K \le 1.783$ proof of Grothendieck's inequality (Section 3.7) rely on.
--
--   Let $(\Omega, \mathcal F, P)$ be a probability space, $n \in \mathbb N$, and let $g \sim
--   N(0, I_n)$ be a standard Gaussian random vector in $\mathbb R^n$ (the companion definition
--   `IsStandardGaussianVector`). For any fixed unit vectors $u, v \in S^{n-1}$,
--
--   $$
--   \mathbb E \bigl[\operatorname{sign}\langle g, u\rangle \, \operatorname{sign}\langle g,
--   v\rangle\bigr] \;=\; \frac{2}{\pi} \arcsin\langle u, v\rangle .
--   $$
--
--   Geometrically, $\operatorname{sign}\langle g, u\rangle$ records which side of the
--   hyperplane through the origin orthogonal to $u$ the point $g$ falls on; the identity says
--   the correlation of these two random signs is a simple, explicit (though nonlinear) function
--   of the angle between $u$ and $v$.
--
--   **Formalization Note** $\langle g, u \rangle$ and $\langle g, v \rangle$ are the coordinate
--   inner products $\sum_i g_i u_i$ and $\sum_i g_i v_i$; unit-norm is stated as $\sum_i u_i^2 =
--   1$ (equivalently $\|u\|_2 = 1$). `Real.sign` is Mathlib's real sign function, returning $0$
--   exactly at $0$; since $\langle g, u\rangle$ and $\langle g, v\rangle$ are a.s. nonzero for
--   $u, v \neq 0$ (a standard Gaussian vector assigns probability $0$ to any fixed hyperplane),
--   this convention agrees with the book's $\{-1,+1\}$-valued sign almost everywhere and does
--   not affect the expectation.
-- source:
--   Vershynin, High-Dimensional Probability (2018), Lemma 3.6.6, p. 69 (PDF p. 77)

import Mathlib
import Definitions.Def_HighDimProb_RandomVectors_IsStandardGaussianVector

open MeasureTheory ProbabilityTheory

namespace HighDimProb.RandomVectors

/-- **Lemma 3.6.6** (Grothendieck's identity), Vershynin, *High-Dimensional Probability*
(2018), p. 69.

Consider a random vector `g ∼ N(0, Iₙ)`. Then, for any fixed vectors `u, v ∈ Sⁿ⁻¹`, we have

`E [sign⟨g, u⟩ sign⟨g, v⟩] = (2/π) arcsin⟨u, v⟩`. -/
theorem grothendieck_identity :
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      {n : ℕ} (g : Fin n → Ω → ℝ), IsStandardGaussianVector P g →
      ∀ u v : Fin n → ℝ, (∑ i, (u i) ^ 2 = 1) → (∑ i, (v i) ^ 2 = 1) →
        ∫ ω, Real.sign (∑ i, g i ω * u i) * Real.sign (∑ i, g i ω * v i) ∂P =
          (2 / Real.pi) * Real.arcsin (∑ i, u i * v i) := by sorry

end HighDimProb.RandomVectors
