-- Prove2me | Theorems.Thm_L0BnB_DualGap_proposition_3
-- name    : L0BnB.DualGap.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:28:26.258215+00:00
-- url     : https://prove2.me/theorems/53e7b5a0-e51b-499c-9ab7-c2920a170bf3
-- title:
--   Proposition 3 — the violation set V of Algorithm 2 is a correlation threshold test
-- statement:
--   Let $X\in\mathbb R^{n\times p}$ have columns of unit $\ell_2$ norm, $y\in\mathbb R^n$, $\lambda_0,\lambda_2,M>0$, and let $\hat\beta\in\mathbb R^p$ with residual $\hat r=y-X\hat\beta$. Then the set $V$ of Step 2 of Algorithm 2 (the coordinates $i\notin\operatorname{Supp}(\hat\beta)$ at which $0$ is not a minimizer of $\beta_i\mapsto F(\hat\beta_1,\dots,\beta_i,\dots,\hat\beta_p)$ over $|\beta_i|\le M$) can be written as
--   $$
--   V=\{\,i\in\operatorname{Supp}(\hat\beta)^c \;:\; |\langle\hat r,X_i\rangle|>c(\lambda_0,\lambda_2,M)\,\},\qquad(17)
--   $$
--   where $c(\lambda_0,\lambda_2,M)=2\sqrt{\lambda_0\lambda_2}$ if $\sqrt{\lambda_0/\lambda_2}\le M$ and $c(\lambda_0,\lambda_2,M)=\lambda_0/M+\lambda_2M$ if $\sqrt{\lambda_0/\lambda_2}>M$.
--
--   The proposition turns the optimality check of Algorithm 2 into a test on correlations with the residual. It is what makes $V=\emptyset$ usable in the dual-bound analysis.
--
--   **Formalization Note** The unit-norm assumption on the columns of $X$ is the standing assumption of Section 3 of the paper; the unit norm of $y$ is not needed here and is not assumed. $\hat\beta$ is an arbitrary vector: the identity does not use that it comes from Algorithm 2.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, p. 12, Proposition 3, (17); proof p. 30; standing assumption p. 9

import Mathlib
import Definitions.Def_L0BnB_DualGap_Setup

namespace L0BnB.DualGap

/-- Proposition 3, p. 12: with `r̂ = y − Xβ̂` and unit-norm columns of `X`,
`V = {i ∈ Supp(β̂)ᶜ | |⟨r̂, Xᵢ⟩| > c(λ₀, λ₂, M)}` (17). -/
theorem proposition_3 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M)
    (hX : ∀ i, ∑ r, X r i ^ 2 = 1) (βhat : Fin p → ℝ) :
    Vset X y lam0 lam2 M βhat =
      Finset.univ.filter
        (fun i => βhat i = 0 ∧ cThr lam0 lam2 M < |colInner X (resid X y βhat) i|) := by sorry

end L0BnB.DualGap
