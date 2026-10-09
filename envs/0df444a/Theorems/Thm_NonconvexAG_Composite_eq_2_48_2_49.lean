-- Prove2me | Theorems.Thm_NonconvexAG_Composite_eq_2_48_2_49
-- name    : NonconvexAG.Composite.eq_2_48_2_49
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:35:26.879985+00:00
-- url     : https://prove2.me/theorems/3516de5b-42c2-460e-98df-924e5239d57a
-- title:
--   (2.48)–(2.49) — three-point inequalities for the prox steps of Algorithm 2
-- statement:
--   Let $\mathcal X$ be convex on its domain $K$ and let $\mathcal P$ be a prox map for $\mathcal X$ as in (2.37). Run Algorithm 2 with any gradient map $\nabla\Psi$, step sizes with $\alpha_1=1$, $\alpha_k\in(0,1)$ ($k\ge2$), $\beta_k,\lambda_k>0$, and any $x_0$. Then for every $k\ge1$ and every $x\in K$:
--   $$\langle\nabla\Psi(x^{md}_k),x_k-x\rangle+\mathcal X(x_k)\le\mathcal X(x)+\frac1{2\lambda_k}\Big[\|x_{k-1}-x\|^2-\|x_k-x\|^2-\|x_k-x_{k-1}\|^2\Big],$$
--   $$\langle\nabla\Psi(x^{md}_k),x^{ag}_k-x\rangle+\mathcal X(x^{ag}_k)\le\mathcal X(x)+\frac1{2\beta_k}\Big[\|x^{md}_k-x\|^2-\|x^{ag}_k-x\|^2-\|x^{ag}_k-x^{md}_k\|^2\Big].$$
--
--   These are the optimality conditions of the subproblems (2.40) and (2.41), in the three-point form of Lemma 2 of Lan's reference [11].
--
--   **Formalization Note** The paper says "for any $x\in\mathbb R^n$"; for $x\notin K$ the right-hand side is $+\infty$ and the inequality is void, so the statement quantifies over $x\in K$.
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, p. 12, (2.48) and (2.49)

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_NonconvexAG_Composite_ProxMap
import Definitions.Def_NonconvexAG_Composite_AGRun

namespace NonconvexAG.Composite

open ConvexOptAlg.SmoothGD

/-- (2.48) and (2.49), p. 12: the three-point inequalities for the prox subproblems (2.40) and
(2.41) of Algorithm 2, for every `k ≥ 1` and every `x` in the domain `K` of `𝒳`. -/
theorem eq_2_48_2_49 {n : ℕ} (gΨ : NonconvexAG.Smooth.E n → NonconvexAG.Smooth.E n) (K : Set (NonconvexAG.Smooth.E n)) (X : NonconvexAG.Smooth.E n → ℝ)
    (hX : ConvexOn ℝ K X) (P : NonconvexAG.Smooth.E n → NonconvexAG.Smooth.E n → ℝ → NonconvexAG.Smooth.E n) (hP : IsProxMap K X P)
    (α β lam : ℕ → ℝ) (hstep : NonconvexAG.Smooth.AGStepsizes α β lam) (x0 : NonconvexAG.Smooth.E n) :
    let xk : ℕ → NonconvexAG.Smooth.E n := xSeq gΨ P α β lam x0
    let xag : ℕ → NonconvexAG.Smooth.E n := xagSeq gΨ P α β lam x0
    let xmd : ℕ → NonconvexAG.Smooth.E n := xmdSeq gΨ P α β lam x0
    ∀ k, 1 ≤ k → ∀ x ∈ K,
      inner ℝ (gΨ (xmd k)) (xk k - x) + X (xk k) ≤
          X x + 1 / (2 * lam k) * (‖xk (k - 1) - x‖ ^ 2 - ‖xk k - x‖ ^ 2 - ‖xk k - xk (k - 1)‖ ^ 2) ∧
        inner ℝ (gΨ (xmd k)) (xag k - x) + X (xag k) ≤
          X x + 1 / (2 * β k) * (‖xmd k - x‖ ^ 2 - ‖xag k - x‖ ^ 2 - ‖xag k - xmd k‖ ^ 2) := by sorry
end NonconvexAG.Composite
