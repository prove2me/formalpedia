-- Prove2me | Theorems.Thm_OnlineConvexOpt_OnlineBoosting_smoothed_regret_comparison
-- name    : OnlineConvexOpt.OnlineBoosting.smoothed_regret_comparison
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T20:50:53.770222+00:00
-- url     : https://prove2.me/theorems/6efac277-d14e-4a2b-91fb-f44a71eb3efa
-- title:
--   Lemma 12.5 — smoothed-loss regret comparison
-- statement:
--   **Statement (Lemma 12.5, p. 201, PDF p. 223).** For smoothed loss functions $\{\hat f_t\}$
--   that are `β`-smooth and `Ĝ`-Lipschitz, $\sum_{t=1}^T \hat f_t(x^N_t) - \sum_{t=1}^T \hat
--   f_t(x^\star_t) \le \frac{2\beta D^2 T}{\gamma^2 N} + \frac{\hat G D}\gamma \mathrm{Regret}_T(W)$.
--
--   This is the main technical lemma behind Theorem 12.4: it bounds how far Algorithm 36's
--   stage-`N` iterate is (in extended-loss value) from the best hypothesis in `CH(H)`'s own
--   decisions, using the offline Frank-Wolfe analysis technique (as in Chunk 07's Theorem 7.1)
--   applied to the cascade of `N` weak-learner stages instead of a single gradient-descent
--   sequence.
--
--   **Formalization Note.** Drafted with `x^N`, `x⋆`, and `Regret_T(W)` as explicit inputs — the
--   level of abstraction the book's own proof of this lemma uses, before Theorem 12.4
--   instantiates `β = dG/δ`, `Ĝ = G`.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 201, Lemma 12.5 (PDF p. 223)

import Mathlib
import Definitions.Def_OnlineConvexOpt_OnlineBoosting_SmoothOn

namespace OnlineConvexOpt.OnlineBoosting

/-- Lemma 12.5 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 201, PDF p. 223). For smoothed loss functions `{f̂_t}` that are
`β`-smooth and `Ĝ`-Lipschitz, `∑_{t=1}^T f̂_t(x^N_t) - ∑_{t=1}^T f̂_t(x⋆_t) ≤
(2βD²T)/(γ²N) + (ĜD/γ)Regret_T(W)`.

`x^N_t` is Algorithm 36's stage-`N` iterate (before the final projection); `x⋆_t = h⋆(a_t)` for
`h⋆ = arg min_{h⋆∈CH(H)}∑f_t(h⋆(a_t))`, the best hypothesis in the convex hull of `H` in
hindsight. This lemma is the main technical step feeding Theorem 12.4; drafted here with `x^N`,
`x⋆`, and `Regret_T(W)` as explicit inputs (the level of abstraction the book's own proof of
this lemma uses, before Theorem 12.4 instantiates `β = dG/δ`, `Ĝ = G`). -/
theorem smoothed_regret_comparison
    {n : ℕ} (D γ : ℝ) (hDpos : 0 < D) (hγpos : 0 < γ) (hγ1 : γ ≤ 1)
    (N T : ℕ) (hN : 0 < N) (hT : 0 < T)
    (fhat : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (β Ghat : ℝ) (hβpos : 0 < β) (hGhatpos : 0 < Ghat)
    (ghat : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hsmooth : ∀ t, SmoothOn Set.univ (fhat t) (ghat t) β)
    (hLip : ∀ t, ∀ x y, |fhat t x - fhat t y| ≤ Ghat * dist x y)
    (xN xstar : ℕ → EuclideanSpace ℝ (Fin n)) (RegretBoundW : ℝ) :
    (∑ t ∈ Finset.Icc 1 T, fhat t (xN t)) - ∑ t ∈ Finset.Icc 1 T, fhat t (xstar t) ≤
      (2 * β * D ^ 2 * T) / (γ ^ 2 * N) + (Ghat * D / γ) * RegretBoundW := by sorry

end OnlineConvexOpt.OnlineBoosting
