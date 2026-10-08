-- Prove2me | Theorems.Thm_OnlineConvexOpt_Regularization_rftl_regret_via_stability_v2
-- name    : OnlineConvexOpt.Regularization.rftl_regret_via_stability_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:41:21.741983+00:00
-- url     : https://prove2.me/theorems/8497e072-b8ad-40fc-a107-4e853de35a67
-- title:
--   Lemma 5.3 — RFTL regret via prediction stability (convex costs, bounded $K$, corrected regret)
-- statement:
--   **Statement (Lemma 5.3).** Let $K$ be a nonempty, bounded, convex decision set in a real Hilbert space, $R$ a regularizer bounded on $K$ (so that $D_R^2=\max_{x,y\in K}(R(x)-R(y))$ is finite), $\eta>0$, and $f_0,f_1,\dots$ cost functions convex on $K$. Let $(x,\nabla)$ be a run of the RFTL algorithm (Algorithm 13). Then for every horizon $T$,
--   $$\mathrm{Regret}_T\;\le\;\sum_{t=1}^{T}\nabla_t^\top(x_t-x_{t+1})+\frac1\eta D_R^2 .$$
--
--   **Formalization Note.** The retired statement dropped the OCO standing assumption that the costs are convex on $K$ (used in Eq. (5.1)); a non-convex cost with a stationary iterate refuted it. The new statement adds convexity of the $f_t$ together with Algorithm 13's input assumptions on $K$ (nonempty, bounded, convex), and uses `RegretT` from `OnlineConvexOpt_FirstOrder_Protocol_v2`, which subtracts the real infimum of the cumulative cost over $K$ instead of the retired junk-valued `⨅ y ∈ K` binder; under the hypotheses that infimum is genuine (each $f_t$ is convex on the bounded set $K$ with a gradient at $x_t\in K$). $D_R^2$ is `RDiameterSq` of the re-issued `OnlineConvexOpt_Regularization_Protocol_v2`, the real supremum of $\{R(x)-R(y):x,y\in K\}$, guarded by the explicit hypothesis `hRbdd` as before. Rounds are $0$-indexed.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 75, Lemma 5.3 (PDF p. 97)

import Mathlib
import Definitions.Def_OnlineConvexOpt_Regularization_Protocol_v2
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol_v2

open scoped InnerProductSpace
open OnlineConvexOpt.Regularization OnlineConvexOpt.FirstOrder

namespace OnlineConvexOpt.Regularization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Lemma 5.3 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 75, PDF p. 97). A run of the RFTL algorithm (Algorithm 13, with
regularizer `R`, step size `η > 0`) on convex cost functions `f` over the bounded convex
decision set `K` satisfies, for every horizon `T`,
`RegretT ≤ Σ_{t=1}^T ∇_t^⊤(x_t - x_{t+1}) + (1/η) D_R²` — in the chapter's 0-indexed
convention (round `t ∈ ℕ` is the book's round `t + 1`),
`Σ_{t ∈ range T} ⟪grad t, x t - x (t + 1)⟫ + (1/η) * D_R²`. `hRbdd` guards `RDiameterSq`'s
defining supremum (the book's `D_R` presupposes `R` bounded on `K`).

Corrected version: the retired statement dropped the OCO standing assumptions that the costs
`f_t` are convex on `K` (used in the proof's first step, Eq. (5.1)) and that `K` is a nonempty
bounded convex set (Algorithm 13's input, "a bounded, convex and closed set `K`"); `RegretT` is
now the `OnlineConvexOpt_FirstOrder_Protocol_v2` regret (genuine infimum over `K`), which under
these hypotheses is the book's `min` (the cumulative cost is bounded below on the bounded set
`K` by convexity at `x_t ∈ K` and the gradient there). -/
theorem rftl_regret_via_stability_v2
    (K : Set E) (hKconv : Convex ℝ K) (hKne : K.Nonempty) (hKbdd : Bornology.IsBounded K)
    (R : E → ℝ) (gradR : E → E) (η : ℝ) (hη : 0 < η)
    (f : ℕ → E → ℝ) (hfconv : ∀ t, ConvexOn ℝ K (f t))
    (x grad : ℕ → E) (hRun : IsRFTLRun K R η f x grad)
    (hRbdd : BddAbove (Set.image2 (fun p q => R p - R q) K K)) (T : ℕ) :
    RegretT K f x T ≤
      (∑ t ∈ Finset.range T, ⟪grad t, x t - x (t + 1)⟫_ℝ) + (1 / η) * RDiameterSq R K := by sorry

end OnlineConvexOpt.Regularization
