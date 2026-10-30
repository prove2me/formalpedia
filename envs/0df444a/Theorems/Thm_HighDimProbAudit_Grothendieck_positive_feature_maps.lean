-- Prove2me | Theorems.Thm_HighDimProbAudit_Grothendieck_positive_feature_maps
-- name    : HighDimProbAudit.Grothendieck.positive_feature_maps
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:36:28.909165+00:00
-- url     : https://prove2.me/theorems/2fb279f5-99c1-4c4f-92e0-ea24a00a5976
-- title:
--   Exercise 3.7.5(a)–(c) — positive coefficient feature maps
-- statement:
--   Fix $n\in\mathbb N$. Each of the following assertions holds.
--
--   1. There are a real Hilbert space $H$ and a transformation $\Phi:\mathbb R^n\to H$ such that
--   $$\langle\Phi(u),\Phi(v)\rangle=2\langle u,v\rangle^2+5\langle u,v\rangle^3\qquad(u,v\in\mathbb R^n).$$
--   2. For every real polynomial $p$ whose coefficients are nonnegative, there are a real Hilbert space $H$ and a transformation $\Phi:\mathbb R^n\to H$ such that
--   $$\langle\Phi(u),\Phi(v)\rangle=p(\langle u,v\rangle)\qquad(u,v\in\mathbb R^n).$$
--   3. For every real function $f$ with one globally convergent representation $f(x)=\sum_{k=0}^\infty a_kx^k$ and $a_k\ge0$ for all $k$, there are a real Hilbert space $H$ and a transformation $\Phi:\mathbb R^n\to H$ such that
--   $$\langle\Phi(u),\Phi(v)\rangle=f(\langle u,v\rangle)\qquad(u,v\in\mathbb R^n).$$
--
--   In each part the space and map are chosen once for the given dimension and polynomial or series, and work simultaneously for every input pair. The three clauses retain the entire numbered exercise, including its analytic part. No linearity of the transformation is asserted.
--
--   Differences from the source:
--   - encoding: vectors in ℝⁿ with their Euclidean inner product → EuclideanSpace ℝ (Fin n); reason: Fin n relabels the finite coordinates; the norm and inner product are the Euclidean ones
--   - encoding: there exist a Hilbert space H and transformations → existential carrier H, normed additive group and real inner product structures, completeness, then maps; reason: the chosen structures specify the real Hilbert space before every input vector; no linearity, continuity, separability or finite dimension is imposed
--   - encoding: a single convergent power series (3.29) for every real x → GlobalPowerSeries a f, namely ∀ x : ℝ, HasSum (fun k => a k * x ^ k) (f x); reason: this is the source’s global series convention, rather than merely local real analyticity or a total infinite sum
-- source:
--   Vershynin, High-Dimensional Probability: An Introduction with Applications in Data Science, Cambridge University Press, 2018, author-corrected electronic copy dated June 9, 2020, https://doi.org/10.1017/9781108231596, Exercise 3.7.5(a)–(c), Eq. (3.29), starts printed p. 71 (PDF p. 79), continues printed p. 72 (PDF p. 80).

import Mathlib
import Definitions.Def_HighDimProbAudit_Grothendieck_GlobalSeries

set_option autoImplicit false

namespace HighDimProbAudit.Grothendieck

/-- Exercise 3.7.5(a), (b), and (c), printed pp. 71–72 / PDF pp. 79–80. -/
theorem positive_feature_maps (n : ℕ) :
    (∃ (H : Type) (hN : NormedAddCommGroup H),
      letI := hN
      ∃ hI : InnerProductSpace ℝ H,
        letI := hI
        CompleteSpace H ∧ ∃ Φ : EuclideanSpace ℝ (Fin n) → H,
          ∀ u v, inner ℝ (Φ u) (Φ v) =
            2 * (inner ℝ u v) ^ 2 + 5 * (inner ℝ u v) ^ 3) ∧
    (∀ p : Polynomial ℝ, (∀ k : ℕ, 0 ≤ p.coeff k) →
      ∃ (H : Type) (hN : NormedAddCommGroup H),
        letI := hN
        ∃ hI : InnerProductSpace ℝ H,
          letI := hI
          CompleteSpace H ∧ ∃ Φ : EuclideanSpace ℝ (Fin n) → H,
            ∀ u v, inner ℝ (Φ u) (Φ v) = p.eval (inner ℝ u v)) ∧
    (∀ (a : ℕ → ℝ) (f : ℝ → ℝ), GlobalPowerSeries a f → (∀ k, 0 ≤ a k) →
      ∃ (H : Type) (hN : NormedAddCommGroup H),
        letI := hN
        ∃ hI : InnerProductSpace ℝ H,
          letI := hI
          CompleteSpace H ∧ ∃ Φ : EuclideanSpace ℝ (Fin n) → H,
            ∀ u v, inner ℝ (Φ u) (Φ v) = f (inner ℝ u v)) := by sorry

end HighDimProbAudit.Grothendieck
