-- Prove2me | Theorems.Thm_OnlineConvexOpt_OnlineBoosting_extension_approximation_and_monotonicity
-- name    : OnlineConvexOpt.OnlineBoosting.extension_approximation_and_monotonicity
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T20:50:24.320986+00:00
-- url     : https://prove2.me/theorems/bffc31ff-d2fa-4f48-8a54-8217dad52737
-- title:
--   Lemma 12.3 — extension operator approximation and monotonicity
-- statement:
--   **Statement (Lemma 12.3, p. 199, PDF p. 221).** The `(K,κ,δ)`-extension of a function
--   $\hat f = X[f]$ satisfies: (1) for every point $x\in K$, $|\hat f(x)-f(x)| \le \delta G$;
--   (2) the projection of a point (whose gradient is bounded by $G$) onto $K$ improves the
--   extension's value, for $\kappa=G$, up to a small term: $\hat f(\Pi_K(x)) \le \hat f(x) +
--   \delta G$.
--
--   This is the technical engine behind Algorithm 36's ability to use a proxy loss defined
--   everywhere on $\mathbb R^d$: it costs at most $\delta G$ per use to move a point into $K$ by
--   projection, and the extension's value on $K$ never drifts from the true loss by more than
--   $\delta G$ either.
--
--   **Formalization Note.** The book's own display writes `‖f̂(x)-f(x)‖₂` for a real-valued
--   quantity; rendered as `|·|`.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 199, Lemma 12.3 (PDF p. 221)

import Mathlib
import Definitions.Def_OnlineConvexOpt_OnlineBoosting_Extension
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol

open OnlineConvexOpt.FirstOrder

namespace OnlineConvexOpt.OnlineBoosting

/-- Lemma 12.3 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 199, PDF p. 221). The `(K,κ,δ)`-extension of a function `f̂ = X[f]`
satisfies: (1) for every `x ∈ K`, `|f̂(x) - f(x)| ≤ δG`; (2) for `κ = G`, the projection of a
point (whose gradient is bounded by `G`) onto `K` improves the extension's value up to `δG`:
`f̂(Π_K(x)) ≤ f̂(x) + δG`. -/
theorem extension_approximation_and_monotonicity
    {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hKconv : Convex ℝ K) (hKne : K.Nonempty)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (G δ : ℝ) (hGpos : 0 < G) (hδpos : 0 < δ)
    (hfG : ∀ x, ∀ v, HasGradientAt f v x → ‖v‖ ≤ G) :
    (∀ x ∈ K, |Extension K G δ f x - f x| ≤ δ * G) ∧
    (∀ x xπ : EuclideanSpace ℝ (Fin n), IsMetricProjection K x xπ →
      Extension K G δ f xπ ≤ Extension K G δ f x + δ * G) := by sorry

end OnlineConvexOpt.OnlineBoosting
