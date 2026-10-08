-- Prove2me | Theorems.Thm_GassSaaty_ParametricPivot_ineq3_iff_interval
-- name    : GassSaaty.ParametricPivot.ineq3_iff_interval
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:42:14.893564+00:00
-- url     : https://prove2.me/theorems/cc2c2464-b889-4dd7-a79b-5e6ca0fd69ec
-- title:
--   Eqs. (3)–(5) — when (3) is consistent, $\alpha_j + \lambda\beta_j \le 0$ for all $j$ iff $\underline\lambda \le \lambda \le \bar\lambda$
-- statement:
--   Let $B$ be a basis and $\alpha_j, \beta_j$ ($j = 1, \dots, n$) the coefficients of $z_j - c_j = \alpha_j + \lambda\beta_j$ for the parametric cost $d + \lambda d'$. Let
--
--   $$
--   \underline\lambda = \max_{\beta_j < 0}\Big(-\frac{\alpha_j}{\beta_j}\Big) \ (\,-\infty \text{ if all } \beta_j \ge 0), \qquad \bar\lambda = \min_{\beta_j > 0}\Big(-\frac{\alpha_j}{\beta_j}\Big) \ (\,+\infty \text{ if all } \beta_j \le 0). \qquad (5)
--   $$
--
--   Suppose the inequalities (3) are consistent, that is, some $\lambda_0$ satisfies $\alpha_j + \lambda_0 \beta_j \le 0$ for all $j$ (Case A). Then for every real $\lambda$,
--
--   $$
--   \alpha_j + \lambda\beta_j \le 0 \ \ (j = 1,\dots,n) \iff \underline\lambda \le \lambda \le \bar\lambda. \qquad (4)
--   $$
--
--   This is the "i.e." of p. 40: the set of $\lambda$ satisfying (3) is the closed interval (4) with endpoints (5). The consistency hypothesis is needed: an index with $\beta_j = 0$ and $\alpha_j > 0$ makes (3) empty while (5) is unaffected.
--
--   **Formalization Note** $\underline\lambda$ is `lamLower` in `WithBot ℝ` and $\bar\lambda$ is `lamBar` in `WithTop ℝ`; the comparisons are made after casting $\lambda$ into these types, so the infinite cases of (5) are represented exactly. The statement holds for any basis indices and needs no feasibility: it is a fact about the numbers $\alpha_j, \beta_j$.
-- source:
--   Gass and Saaty, The computational algorithm for the parametric objective function, Naval Res. Logist. Quart. 2 (1955), p. 40, Section 2, Case A, Eqs. (3), (4), (5)

import Mathlib
import Definitions.Def_GassSaaty_ParametricPivot_Parametric

open LinearOptimization

namespace GassSaaty.ParametricPivot

theorem ineq3_iff_interval {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (d d' : Fin n → ℝ) (B : Fin m ↪ Fin n)
    (hcons : ∃ t₀ : ℝ, ∀ j, alpha A d B j + t₀ * beta A d' B j ≤ 0) (t : ℝ) :
    (∀ j, alpha A d B j + t * beta A d' B j ≤ 0) ↔
      (lamLower A d d' B ≤ (t : WithBot ℝ) ∧ (t : WithTop ℝ) ≤ lamBar A d d' B) := by sorry

end GassSaaty.ParametricPivot
