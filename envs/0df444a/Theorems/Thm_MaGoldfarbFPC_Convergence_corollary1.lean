-- Prove2me | Theorems.Thm_MaGoldfarbFPC_Convergence_corollary1
-- name    : MaGoldfarbFPC.Convergence.corollary1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:41:57.336989+00:00
-- url     : https://prove2.me/theorems/58544549-ad2c-4aa4-852b-49d6afede4ee
-- title:
--   Corollary 1 — X* is optimal for (1.8) iff X* = S_{τμ}(h(X*))
-- statement:
--   Let $\mathcal A:\mathbb R^{m\times n}\to\mathbb R^p$ be linear, $b\in\mathbb R^p$, $\mu>0$ and $\tau>0$. Let $g(X)=\mathcal A^*(\mathcal A(X)-b)$, $h(X)=X-\tau g(X)$, and let $S_\nu$ be the matrix shrinkage operator. Then a matrix $X^*\in\mathbb R^{m\times n}$ is an optimal solution of problem (1.8), $\min_X\mu\|X\|_*+\tfrac12\|\mathcal A(X)-b\|_2^2$, if and only if
--   $$X^*=S_{\tau\mu}\big(h(X^*)\big).$$
--
--   It characterizes the optimal set $\mathcal X^*$ as the fixed point set of the map $X\mapsto S_{\tau\mu}(h(X))$ that the iterations (2.1) apply, for every step $\tau>0$.
--
--   **Formalization Note** The paper states the corollary after "for any $\tau>0$" (p. 8), with $\mu>0$ implicit in $\nu=\tau\mu>0$; both are explicit hypotheses, and there is no upper bound on $\tau$. $X^*=S_{\tau\mu}(h(X^*))$ is `IsShrink (τ * μ) (h τ Aop b Xs) Xs`: $X^*$ is the shrinkage of $h(X^*)$ for some reduced SVD of $h(X^*)$. Since the shrinkage does not depend on the SVD chosen, "some" and "every" agree here.
-- source:
--   Ma, Goldfarb and Chen, Fixed point and Bregman iterative methods for matrix rank minimization, arXiv:0905.1643v2, p. 9, Corollary 1 (with (2.10)–(2.12), p. 8)

import Mathlib
import Definitions.Def_MaGoldfarbFPC_Convergence_Basic

namespace MaGoldfarbFPC.Convergence

open CaiCandesShen.Convergence

/-- Corollary 1, p. 9: for `μ > 0` and any step `τ > 0`, `X*` is an optimal solution of
(1.8) if and only if `X* = S_{τμ}(h(X*))`, where `h(·) = I(·) − τg(·)`. -/
theorem corollary1 {m n p : ℕ} (Aop : Fin p → Mat m n) (b : Fin p → ℝ) (μ τ : ℝ)
    (hμ : 0 < μ) (hτ : 0 < τ) (Xs : Mat m n) :
    IsOptimal μ Aop b Xs ↔ IsShrink (τ * μ) (h τ Aop b Xs) Xs := by sorry

end MaGoldfarbFPC.Convergence
