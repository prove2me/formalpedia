-- Prove2me | Theorems.Thm_MvPolynomial_abv_eval_sub_eval_le_mul_iSup
-- name    : MvPolynomial.abv_eval_sub_eval_le_mul_iSup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/c6fb7222-3f9f-51a4-8a07-a765b92b9ded
-- title:
--   Non-archimedean Lipschitz bound for polynomials on the unit polydisc
-- statement:
--   Let $K$ be a field and $\mu : K \to \mathbb{R}$ an absolute value which is non-archimedean, i.e. satisfies $\mu(a+b) \le \max(\mu(a),\mu(b))$ for all $a,b$. Fix $r \in \mathbb{N}$ and a polynomial $G \in K[X_0,\dots,X_{r-1}]$ in $r$ variables indexed by `Fin r`, and a real number $C$ bounding all coefficients of $G$ in the sense that $\mu(G_m) \le C$ for every exponent multi-index $m : \mathrm{Fin}\,r \to_0 \mathbb{N}$ (in particular $C \ge 0$, since $\mu$ is non-negative). Let $x, v : \mathrm{Fin}\,r \to K$ be two points of the closed unit polydisc, i.e. $\mu(x_l) \le 1$ and $\mu(v_l) \le 1$ for every coordinate $l$. The conclusion is the estimate $$\mu\bigl(G(x) - G(v)\bigr) \le C \cdot \sup_l \mu(x_l - v_l),$$ where $G(x)$ and $G(v)$ denote the evaluations of $G$ at $x$ and at $v$, and the supremum is the indexed supremum over `Fin r` of the reals $\mu(x_l - v_l)$ (a finite, hence attained, supremum when $r > 0$; for $r = 0$ it is the supremum of the empty family).
--
--   This is the ultrametric mean-value estimate: a polynomial with coefficients of absolute value at most $C$ is $C$-Lipschitz on the closed unit polydisc with respect to the sup-coordinate distance $\max_l \mu(x_l - v_l)$. It is used in the analysis of evaluation of forms at normalised coordinate vectors of points on a modular curve, via [`ModularCurve.exists_log_absValue_evalAt_ge_of_forall_prox_le`](thm.html#ModularCurve.exists_log_absValue_evalAt_ge_of_forall_prox_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPolynomial_abv_eval_sub_eval_le_mul_iSup.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem MvPolynomial.abv_eval_sub_eval_le_mul_iSup
    {K : Type*} [Field K] (μ : AbsoluteValue K ℝ) (hμ : IsNonarchimedean μ)
    {r : ℕ} (G : MvPolynomial (Fin r) K) (C : ℝ) (hC : ∀ m, μ (G.coeff m) ≤ C)
    (x v : Fin r → K) (hx : ∀ l, μ (x l) ≤ 1) (hv : ∀ l, μ (v l) ≤ 1) :
    μ (MvPolynomial.eval x G - MvPolynomial.eval v G) ≤ C * ⨆ l, μ (x l - v l) := by sorry
