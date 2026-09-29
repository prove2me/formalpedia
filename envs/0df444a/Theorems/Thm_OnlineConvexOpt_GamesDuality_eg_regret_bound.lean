-- Prove2me | Theorems.Thm_OnlineConvexOpt_GamesDuality_eg_regret_bound
-- name    : OnlineConvexOpt.GamesDuality.eg_regret_bound
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-18T05:21:42.652588+00:00
-- url     : https://prove2.me/theorems/da6d12b2-aaaf-48a8-8823-711ab0f09371
-- title:
--   Eq. (8.1) — EG/Hedge regret bound for Algorithm 28's row player
-- statement:
--   An unnumbered but load-bearing equation of Section 8.3 (Eq. (8.1), p. 145), instantiating the
--   regret bound of the Exponentiated Gradient algorithm (Corollary 5.7 of Chapter 5, "RFTL and
--   the Regret Bound of Follow-the-Regularized-Leader") to Algorithm 28's specific run.
--
--   Let $A \in \mathbb{R}^{n \times m}$ ($n, m \ge 1$), let $T \ge 1$, and let $(x, y)$ be a run
--   of Algorithm 28 on $A$ with learning rate $\eta = \sqrt{2 \log n / T}$ — the row player's
--   mixed strategy starts uniform and updates by the exponentiated-gradient rule on the linear
--   loss $f_t(\cdot) = (\cdot)^{\mathsf T} A y_t$, while the column player best-responds at every
--   round (`IsSimpleLPRun`). Then
--   $$\sum_{t=0}^{T-1} x_t^{\mathsf T} A y_t \;\le\; \min_{x' \in \Delta_n}
--     \sum_{t=0}^{T-1} (x')^{\mathsf T} A y_t \;+\; \sqrt{2 T \log n}.$$
--   This says Algorithm 28's row player has external regret at most $\sqrt{2T \log n}$ against
--   the (adversarially, adaptively chosen) linear loss sequence her own play induces via the
--   column player's best responses.
--
--   **Formalization Note.** Chapter 5's Corollary 5.7 belongs to a different mission of this
--   series and is not imported (per this series' convention, a chapter that needs a fact from
--   another chapter restates it locally rather than importing a sibling draft); this theorem is
--   the local, self-contained restatement of exactly the quantitative content Hazan's proof of
--   Lemma 8.4 uses, cited as it is cited on the page, "Eq. (8.1)". The book's derivation invokes
--   it with "appropriate choice of $\eta$"; that choice is pinned down explicitly here to the
--   value that makes the bound's constant exactly $\sqrt{2T\log n}$, matching Eq. (8.1) verbatim.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 145, Eq. (8.1) (payoff range from Definition 8.2, p. 141)

import Mathlib
import Definitions.Def_OnlineConvexOpt_GamesDuality_Game

namespace OnlineConvexOpt.GamesDuality

/-- **Eq. (8.1)**, Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 145: the row player's cumulative value against Algorithm 28's run
`(x, y)` on `T` rounds is within `√(2T log n)` of the best fixed row strategy's cumulative
value, for the learning rate `η = √(2 log n / T)` chosen via Corollary 5.7 (the exponentiated
gradient regret bound specialized to this run's linear losses `f_t(x) = x⊤A y_t` on the
simplex). -/
theorem eg_regret_bound {n m T : ℕ} (hn : 0 < n) (hm : 0 < m) (hT : 0 < T)
    (A : Matrix (Fin n) (Fin m) ℝ) (hA : ∀ i j, |A i j| ≤ 1)
    (x : ℕ → Fin n → ℝ) (y : ℕ → Fin m → ℝ)
    (hrun : IsSimpleLPRun (Real.sqrt (2 * Real.log (n : ℝ) / (T : ℝ))) A x y) :
    ∑ t ∈ Finset.range T, rowValue A (x t) (y t) ≤
      (⨅ x' ∈ stdSimplex ℝ (Fin n), ∑ t ∈ Finset.range T, rowValue A x' (y t)) +
        Real.sqrt (2 * (T : ℝ) * Real.log (n : ℝ)) := by sorry

end OnlineConvexOpt.GamesDuality
