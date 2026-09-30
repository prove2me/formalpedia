-- Prove2me | Theorems.Thm_InventoryControl_cs_total_cost_convex
-- name    : InventoryControl.cs_total_cost_convex
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:21:50.02521+00:00
-- url     : https://prove2.me/theorems/fa17c897-253b-41ae-a87b-57baf8fe6cca
-- title:
--   Problem 10.1: $\hat C_2(y_2)$ is convex in $y_2$, and it has a minimizer
-- statement:
--   Let $S_1$ satisfy the fractile condition (10.8), with $e_1, e_2 \ge 0$, $b_1 > 0$ and
--   $\sigma > 0$. Then the total cost $\hat C_2$ of Eq. (10.9) is a convex function of the
--   echelon position $y_2$ on $\mathbb{R}$, and, when $e_2 > 0$, it attains its minimum at some
--   $y_2^{*}$.
--
--   Convexity is the content of the book's Problem 10.1: $x \mapsto \hat C_1(\min\{S_1, x\})$ is
--   convex exactly because $S_1$ minimizes the convex function $\hat C_1$, and convexity survives
--   the expectation over $D(L_2)$ and the addition of the linear term $h_2(y_2 - \mu_2')$. For
--   $e_2 > 0$ the minimum exists because $\hat C_2(y_2) \to \infty$ in both directions: like
--   $h_2y_2$ as $y_2 \to \infty$ and like $-b_1y_2$ as $y_2 \to -\infty$.
--
--   The guard $e_2 > 0$ is needed. When $e_2 = h_2 = 0$ and $L_2 \ge 1$, $\hat C_2(y_2)$ is
--   strictly above $\hat C_1(S_1)$ for every $y_2$, because $\hat C_1$ is strictly convex with
--   its unique minimum at $S_1$ and $D(L_2)$ is unbounded, and it tends to $\hat C_1(S_1)$ as
--   $y_2 \to \infty$. So there is no minimizer. This is the upstream mirror of the book's remark
--   that $e_1 = 0$ forces $S_1^{e} \to \infty$ (p. 196): with free upstream holding the optimal
--   $y_2$ runs off to infinity. Convexity is what the book uses to
--   justify searching for a local minimum only, and $y_2^{*}$ is the echelon order-up-to level
--   $S_2^{e}$ of installation 2.
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, p. 196, Sect. 10.1.1: 'It is easy to verify that C-hat2(y2) is convex in y2, which means that we only have to look for a local minimum. Denote the optimal solution by y*2'; Problem 10.1 p. 221

import Definitions.Def_InventoryControl_clarkScarf

namespace InventoryControl

theorem cs_total_cost_convex (e1 e2 b1 mu sigma : ℝ) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) (hb : 0 < b1)
    (hs : 0 < sigma) (L1 L2 : ℕ) (S1 : ℝ)
    (hS1 : ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)
      ((S1 - (L1 + 1) * mu) / (Real.sqrt (L1 + 1) * sigma)) = (e2 + b1) / (e1 + e2 + b1)) :
    ConvexOn ℝ Set.univ (csTotalCost e1 e2 b1 mu sigma L1 L2 S1)
      ∧ (0 < e2 → ∃ S2 : ℝ, ∀ y2 : ℝ, csTotalCost e1 e2 b1 mu sigma L1 L2 S1 S2
          ≤ csTotalCost e1 e2 b1 mu sigma L1 L2 S1 y2) := by sorry

end InventoryControl
