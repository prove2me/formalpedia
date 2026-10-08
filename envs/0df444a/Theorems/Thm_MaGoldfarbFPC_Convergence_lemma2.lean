-- Prove2me | Theorems.Thm_MaGoldfarbFPC_Convergence_lemma2
-- name    : MaGoldfarbFPC.Convergence.lemma2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:42:05.387363+00:00
-- url     : https://prove2.me/theorems/9cefeeb1-6f41-4f73-a741-f2720ccd761c
-- title:
--   Lemma 2 — for τ ∈ (0, 2/λmax(AᵀA)) the gradient step h = I − τg is nonexpansive, with equality iff h(X) − h(X′) = X − X′
-- statement:
--   Let $\mathcal A:\mathbb R^{m\times n}\to\mathbb R^p$ be linear with matrix $A\in\mathbb R^{p\times mn}$, i.e. $\mathcal AX=A\,\mathrm{vec}(X)$, let $b\in\mathbb R^p$, and let $\tau\in(0,2/\lambda_{\max}(A^\top A))$. Let $g(X)=\mathcal A^*(\mathcal A(X)-b)$ and $h(X)=X-\tau g(X)$. Then for all $X,X'\in\mathbb R^{m\times n}$
--   $$\|h(X)-h(X')\|_F\le\|X-X'\|_F,$$
--   and $h(X)-h(X')=X-X'$ if and only if $\|h(X)-h(X')\|_F=\|X-X'\|_F$.
--
--   Together with Lemma 1 it makes the iteration map $X\mapsto S_{\tau\mu}(h(X))$ non-expansive, with a usable description of when distances are preserved.
--
--   **Formalization Note** $\lambda_{\max}(A^\top A)=\|\mathcal A\|_2^2$, and the range is the predicate `StepRange τ Aop`: $0<\tau$ and $\tau\|\mathcal A\|_2^2<2$, which for $\mathcal A=0$ is $(0,\infty)$ as on paper. "Let $\mathcal AX=A\,\mathrm{vec}(X)$" in the paper fixes notation for the matrix of $\mathcal A$; it is not a hypothesis. The statement holds for every $b$.
-- source:
--   Ma, Goldfarb and Chen, Fixed point and Bregman iterative methods for matrix rank minimization, arXiv:0905.1643v2, p. 11, Lemma 2

import Mathlib
import Definitions.Def_MaGoldfarbFPC_Convergence_Basic

namespace MaGoldfarbFPC.Convergence

open CaiCandesShen.Convergence

/-- Lemma 2, p. 11: for `τ ∈ (0, 2/λ_max(AᵀA))` the operator `h(·) = I(·) − τg(·)` is
non-expansive in the Frobenius norm, and `h(X) − h(X′) = X − X′` if and only if
`‖h(X) − h(X′)‖_F = ‖X − X′‖_F`. -/
theorem lemma2 {m n p : ℕ} (Aop : Fin p → Mat m n) (b : Fin p → ℝ) (τ : ℝ)
    (hτ : StepRange τ Aop) (X X' : Mat m n) :
    frobNorm (h τ Aop b X - h τ Aop b X') ≤ frobNorm (X - X') ∧
      (h τ Aop b X - h τ Aop b X' = X - X' ↔
        frobNorm (h τ Aop b X - h τ Aop b X') = frobNorm (X - X')) := by sorry

end MaGoldfarbFPC.Convergence
