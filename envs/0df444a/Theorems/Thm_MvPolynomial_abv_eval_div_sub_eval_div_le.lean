-- Prove2me | Theorems.Thm_MvPolynomial_abv_eval_div_sub_eval_div_le
-- name    : MvPolynomial.abv_eval_div_sub_eval_div_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/a1a2983f-f1c2-5ef6-9255-bf0329235324
-- title:
--   Non-archimedean Lipschitz bound for a rational function near a point
-- statement:
--   Let $K$ be a field and $\mu$ an absolute value on $K$ with values in $\mathbb{R}$ which is non-archimedean, i.e. satisfies the ultrametric inequality. Let $r$ be a natural number and let $A, B \in K[X_1,\dots,X_r]$ be polynomials in $r$ variables, and let $C_A, C_B$ be real numbers such that $\mu(A_m) \le C_A$ and $\mu(B_m) \le C_B$ for every monomial exponent $m$, where $A_m$, $B_m$ denote the corresponding coefficients. Let $x, v \colon \mathrm{Fin}\,r \to K$ be two points of the closed unit polydisc, so $\mu(x_l) \le 1$ and $\mu(v_l) \le 1$ for all $l$, assume $B(v) \neq 0$, and assume the proximity condition $C_B \cdot \bigl(\sup_l \mu(x_l - v_l)\bigr) < \mu(B(v))$, the supremum being the indexed supremum in $\mathbb{R}$ over the index type $\mathrm{Fin}\,r$. The conclusion is the conjunction of two assertions: first, $\mu(B(x)) = \mu(B(v))$; second,
--   $$\mu\!\left(\frac{A(x)}{B(x)} - \frac{A(v)}{B(v)}\right) \le \frac{\max\bigl(C_A\,\mu(B(v)),\; C_B\,\mu(A(v))\bigr)}{\mu(B(v))^2} \cdot \sup_l \mu(x_l - v_l).$$
--   No vanishing or non-vanishing hypothesis is imposed on $A(v)$.
--
--   This is a quantitative, explicitly constant form of the statement that a rational function $A/B$ is Lipschitz for the sup-coordinate ultrametric distance on a neighbourhood of a point $v$ of the closed unit polydisc at which the denominator does not vanish; the first half of the conclusion is the ultrametric equality case, which in particular gives $B(x) \neq 0$. It is used in the study of coordinates on modular curves, for the results [`ModularCurve.JZero.exists_abv_evalAt_eq_abv_evalAt_of_le_prox`](thm.html#ModularCurve.JZero.exists_abv_evalAt_eq_abv_evalAt_of_le_prox) and [`ModularCurve.JZero.exists_one_le_abv_evalAt_of_le_prox`](thm.html#ModularCurve.JZero.exists_one_le_abv_evalAt_of_le_prox).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPolynomial_abv_eval_div_sub_eval_div_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem MvPolynomial.abv_eval_div_sub_eval_div_le
    {K : Type*} [Field K] (μ : AbsoluteValue K ℝ) (hμ : IsNonarchimedean μ)
    {r : ℕ} (A B : MvPolynomial (Fin r) K) (CA CB : ℝ)
    (hA : ∀ m, μ (A.coeff m) ≤ CA) (hB : ∀ m, μ (B.coeff m) ≤ CB)
    (x v : Fin r → K) (hx : ∀ l, μ (x l) ≤ 1) (hv : ∀ l, μ (v l) ≤ 1)
    (hBv : MvPolynomial.eval v B ≠ 0)
    (hclose : CB * (⨆ l, μ (x l - v l)) < μ (MvPolynomial.eval v B)) :
    μ (MvPolynomial.eval x B) = μ (MvPolynomial.eval v B) ∧
      μ (MvPolynomial.eval x A / MvPolynomial.eval x B - MvPolynomial.eval v A / MvPolynomial.eval v B)
        ≤ max (CA * μ (MvPolynomial.eval v B)) (CB * μ (MvPolynomial.eval v A)) / μ (MvPolynomial.eval v B) ^ 2
          * ⨆ l, μ (x l - v l) := by sorry
