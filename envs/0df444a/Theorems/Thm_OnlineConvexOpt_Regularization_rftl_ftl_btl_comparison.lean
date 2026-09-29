-- Prove2me | Theorems.Thm_OnlineConvexOpt_Regularization_rftl_ftl_btl_comparison
-- name    : OnlineConvexOpt.Regularization.rftl_ftl_btl_comparison
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T20:35:49.001035+00:00
-- url     : https://prove2.me/theorems/018f6db5-473a-49cf-bd9b-e4214e3cb673
-- title:
--   Lemma 5.4 — RFTL's FTL/BTL comparison inequality
-- statement:
--   **Statement (Lemma 5.4).** Let $K$ be a decision set, $R$ a regularizer, $\eta > 0$ a step size, $f$ a sequence of cost functions on $K$, and $(x, \mathrm{grad})$ a run of the RFTL algorithm (Algorithm 13). Define, as in the proof of Lemma 5.3, $g_0(x) = \tfrac1\eta R(x)$ and $g_n(x) = \langle \mathrm{grad}_{n-1}, x\rangle$ for $n \ge 1$ (`OnlineConvexOpt.Regularization.gFun`). Then for every horizon $T$ and every $u \in K$,
--   $$\sum_{n=0}^{T} g_n(u) \;\ge\; \sum_{n=0}^{T} g_n(x_n).$$
--
--   This is the "follow-the-leader beats be-the-leader"-type comparison the book proves by induction on $T$: playing the minimizer of the cumulative $g$'s so far is, in total, at least as good as any fixed comparator $u$ measured against the *next* round's cumulative sum. It is the key inequality Lemma 5.3's proof reduces the regret bound to.
--
--   **Formalization Note.** Indices follow this chapter's 0-indexed shift (round $t \in \mathbb{N}$ is the book's round $t+1$): $x_n$ here is the book's $x_{n+1}$, so the conclusion is exactly the book's $\sum_{t=0}^T g_t(u) \ge \sum_{t=0}^T g_t(x_{t+1})$.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 75, Lemma 5.4 (PDF p. 97)

import Mathlib
import Definitions.Def_OnlineConvexOpt_Regularization_Protocol

open scoped InnerProductSpace
open OnlineConvexOpt.Regularization

namespace OnlineConvexOpt.Regularization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Lemma 5.4 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 75, PDF p. 97). With `g_0(x) = (1/η) R(x)` and `g_n(x) = ∇_n^⊤ x` for
`n ≥ 1` (`OnlineConvexOpt.Regularization.gFun`), a run of the RFTL algorithm (Algorithm 13)
satisfies, for every `u ∈ K`, `Σ_{n=0}^{T} g_n(u) ≥ Σ_{n=0}^{T} g_n(x_n)` — `x n` here is the
book's `x_{n+1}` under the chapter's 0-indexed shift, i.e. exactly the book's `Σ_{t=0}^T g_t(u)
≥ Σ_{t=0}^T g_t(x_{t+1})`. -/
theorem rftl_ftl_btl_comparison
    (K : Set E) (R : E → ℝ) (η : ℝ) (hη : 0 < η) (f : ℕ → E → ℝ) (x grad : ℕ → E)
    (hRun : IsRFTLRun K R η f x grad) (T : ℕ) (u : E) (hu : u ∈ K) :
    ∑ n ∈ Finset.range (T + 1), gFun η R grad n u ≥
      ∑ n ∈ Finset.range (T + 1), gFun η R grad n (x n) := by sorry

end OnlineConvexOpt.Regularization
