-- Prove2me | Theorems.Thm_OnlineConvexOpt_Introduction_hedge_loss_bound
-- name    : OnlineConvexOpt.Introduction.hedge_loss_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T05:08:12.625822+00:00
-- url     : https://prove2.me/theorems/7dfbec0a-f9ed-4a38-b03c-08a4f309b965
-- title:
--   Theorem 1.5 — Hedge's loss bound
-- statement:
--   **Theorem 1.5** (Hedge's loss bound, Hazan, p. 12). Let $\ell_t^2$ denote the
--   $N$-dimensional vector of square losses, i.e. $\ell_t^2(i) = \ell_t(i)^2$, let
--   $\varepsilon > 0$, and assume all losses are non-negative. The Hedge algorithm satisfies, for
--   any expert $i^\star \in [N]$,
--
--   $$
--   \sum_{t=1}^T x_t^\top \ell_t \;\le\; \sum_{t=1}^T \ell_t(i^\star) \;+\;
--   \varepsilon \sum_{t=1}^T x_t^\top \ell_t^2 \;+\; \frac{\log N}{\varepsilon}.
--   $$
--
--   This is the chapter's most general guarantee: it drops the binary-mistake restriction of
--   Theorems 1.1–1.4 in favor of arbitrary non-negative real-valued losses, replacing the earlier
--   $(1+\varepsilon)$ multiplicative slack with an explicit additive second-moment correction term
--   $\varepsilon \sum_t x_t^\top \ell_t^2$ that vanishes as losses shrink, and leaves
--   $\varepsilon$ free rather than tuned to a particular horizon.
--
--   **Formalization Note.** `IsHedgeRun` fixes the algorithm's own update rule
--   ($W_{t+1}(i) = W_t(i) e^{-\varepsilon \ell_t(i)}$) as part of the hypothesis, since the bound
--   is meaningful only for this specific update; it is not a black-box regret guarantee that holds
--   for an arbitrary mixed-strategy sequence. `ε` is kept as a free parameter throughout, matching
--   the book's presentation (no substitution of a later corollary's optimized
--   $\varepsilon^\star$).
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 12, Theorem 1.5

import Mathlib import Definitions.Def_OnlineConvexOpt_Introduction_Hedge

namespace OnlineConvexOpt.Introduction

/-- **Theorem 1.5** (Hedge's loss bound), Hazan, *Introduction to Online Convex
Optimization*, 2nd ed., arXiv:1909.05207v3, p. 12.

"Let `ℓ²_t` denote the `N`-dimensional vector of square losses, i.e., `ℓ²_t(i) = ℓ_t(i)²`,
let `ε > 0`, and assume all losses to be non-negative. The Hedge algorithm satisfies for any
expert `i⋆ ∈ [N]`: `∑_{t=1}^T x_t^⊤ ℓ_t ≤ ∑_{t=1}^T ℓ_t(i⋆) + ε ∑_{t=1}^T x_t^⊤ ℓ²_t + log N / ε`." -/
theorem hedge_loss_bound {N : ℕ} (hN : 0 < N) (ε : ℝ) (hε : 0 < ε)
    (ℓ x W : ℕ → Fin N → ℝ) (hnonneg : ∀ t i, 0 ≤ ℓ t i)
    (hrun : IsHedgeRun ε ℓ W x) (T : ℕ) (istar : Fin N) :
    expectedLoss x ℓ T ≤
      expertLoss ℓ istar T + ε * expectedLoss x (fun t i => ℓ t i ^ 2) T + Real.log N / ε := by sorry

end OnlineConvexOpt.Introduction
