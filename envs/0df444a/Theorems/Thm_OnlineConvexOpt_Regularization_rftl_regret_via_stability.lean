-- Prove2me | Theorems.Thm_OnlineConvexOpt_Regularization_rftl_regret_via_stability
-- name    : OnlineConvexOpt.Regularization.rftl_regret_via_stability
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T20:36:29.100803+00:00
-- url     : https://prove2.me/theorems/9318c27c-7b95-4841-b7cc-c705ce130aea
-- title:
--   Lemma 5.3 — RFTL's regret bound via prediction stability
-- statement:
--   **Statement (Lemma 5.3).** Let $K$ be a decision set, $R$ a regularizer with gradient map $\mathrm{gradR}$, $\eta > 0$ a step size, $f$ a sequence of cost functions on $K$, and $(x, \mathrm{grad})$ a run of the RFTL algorithm (Algorithm 13). Then for every horizon $T$,
--   $$\mathrm{Regret}_T \;\le\; \sum_{t=1}^{T} \nabla_t^\top(x_t - x_{t+1}) \;+\; \tfrac{1}{\eta} D_R^2,$$
--   where $D_R^2$ is the $R$-diameter of $K$ (`OnlineConvexOpt.Regularization.RDiameterSq`).
--
--   This bounds the regret of RFTL by the total "prediction drift" $\sum_t \nabla_t^\top(x_t - x_{t+1})$ — how much the algorithm's next prediction differs, along the current gradient direction, from its current one — plus a term controlled by the regularizer's diameter. It is the first of the two steps (with the local-norm bound on the drift term) that together prove Theorem 5.2.
--
--   **Formalization Note.** In the chapter's 0-indexed convention (round $t \in \mathbb{N}$ is the book's round $t+1$), the drift sum is $\sum_{t \in \mathrm{range}\ T} \langle \mathrm{grad}_t, x_t - x_{t+1}\rangle$, and $\mathrm{Regret}_T$ is `OnlineConvexOpt.FirstOrder.RegretT K f x T`, reused as published (Chapter III's mission). The hypothesis `hRbdd : BddAbove (Set.image2 (fun p q => R p - R q) K K)` guards `RDiameterSq`'s defining supremum against Mathlib's junk value ($\mathrm{sSup}$ of an unbounded set is $0$): the book's $D_R$ implicitly presupposes $R$ bounded on $K$, true of every strongly-convex, smooth regularizer over the bounded decision sets §5.1 works with, so this hypothesis narrows nothing the book's proof needs.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 75, Lemma 5.3 (PDF p. 97)

import Mathlib
import Definitions.Def_OnlineConvexOpt_Regularization_Protocol
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol

open scoped InnerProductSpace
open OnlineConvexOpt.Regularization OnlineConvexOpt.FirstOrder

namespace OnlineConvexOpt.Regularization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Lemma 5.3 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 75, PDF p. 97). A run of the RFTL algorithm (Algorithm 13, with
regularizer `R`, gradient map `gradR`, step size `η`) on cost functions `f` over `K` satisfies,
for every horizon `T`, `RegretT ≤ Σ_{t=1}^T ∇_t^⊤(x_t - x_{t+1}) + (1/η) D_R²` — in the
chapter's 0-indexed convention (round `t ∈ ℕ` is the book's round `t + 1`), `Σ_{t ∈ range T}
⟪grad t, x t - x (t + 1)⟫ + (1/η) * D_R²`. `hRbdd` guards `RDiameterSq`'s defining supremum: the
book's `D_R` presupposes `R` bounded on `K` (true for its strongly-convex, smooth regularizers
over the bounded sets §5.1 works with), so without this hypothesis an unbounded `R x - R y`
would make `RDiameterSq` collapse to Mathlib's junk value `0` (`sSup` of an unbounded set),
trivializing the bound (FAITHFULNESS_TRAPS.md trap 5). -/
theorem rftl_regret_via_stability
    (K : Set E) (R : E → ℝ) (gradR : E → E) (η : ℝ) (hη : 0 < η) (f : ℕ → E → ℝ)
    (x grad : ℕ → E) (hRun : IsRFTLRun K R η f x grad)
    (hRbdd : BddAbove (Set.image2 (fun p q => R p - R q) K K)) (T : ℕ) :
    RegretT K f x T ≤
      (∑ t ∈ Finset.range T, ⟪grad t, x t - x (t + 1)⟫_ℝ) + (1 / η) * RDiameterSq R K := by sorry

end OnlineConvexOpt.Regularization
