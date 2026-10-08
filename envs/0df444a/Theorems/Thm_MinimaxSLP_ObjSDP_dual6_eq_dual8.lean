-- Prove2me | Theorems.Thm_MinimaxSLP_ObjSDP_dual6_eq_dual8
-- name    : MinimaxSLP.ObjSDP.dual6_eq_dual8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:09:37.126674+00:00
-- url     : https://prove2.me/theorems/76f6fadc-6c17-459e-8a4c-6030c61b5025
-- title:
--   p. 584 — the dual (6) is reformulated as the semidefinite program (8)
-- statement:
--   Let $W$, $T$, $h$ satisfy Assumption 3 ($\{\pi : W'\pi\le q\}\neq\emptyset$ for every $q\in\mathbb R^d$), let $\alpha_k\ge 0$ for all $k$, and let $x$ have a nonempty recourse set $X(x)$. Then the set of objective values $Q\cdot Y+\mu'y+y_0$ over the feasible points of the dual (6) equals the set of objective values over the feasible points of
--   $$
--   \min_{Y,y,y_0,w_k}\ Q\cdot Y+\mu'y+y_0\quad\text{s.t.}\quad \begin{pmatrix}Y & \tfrac12(y-\alpha_k w_k)\\ \tfrac12(y-\alpha_k w_k)' & y_0-\beta_k\end{pmatrix}\succeq 0,\ \ Ww_k+Tx=h,\ \ w_k\ge 0,\quad k=1,\dots,K. \tag{8}
--   $$
--   In particular $Z_D(x)$ equals the optimal value of (8), and one is attained exactly when the other is.
--
--   This is the reformulation of the second-stage dual as a polynomial-sized semidefinite program; optimizing over $x$ as well gives (7).
--
--   **Formalization Note** The identity is stated for the sets of objective values (which gives the equality of the infima `ZD` and `ZD8` as a second conjunct), so it holds without any assumption on the moments $(\mu,Q)$.
-- source:
--   Bertsimas, Doan, Natarajan & Teo, Models for Minimax Stochastic Linear Optimization Problems with Risk Aversion, Math. Oper. Res. 35(3), 2010, p. 584, (8)

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_MinimaxSLP_ObjSDP_Model

open MeasureTheory Matrix

namespace MinimaxSLP.ObjSDP

/-- p. 584: the dual (6) can be reformulated as the semidefinite program (8). The two programs
have the same set of objective values, hence the same optimal value `Z_D(x)`, attained in one iff
attained in the other. -/
theorem dual6_eq_dual8 {n r d K : ℕ} [NeZero K]
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (α β : Fin K → ℝ) (hα : ∀ k, 0 ≤ α k)
    (μ : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (hrec : (recourseSet W T h x).Nonempty) :
    dualValues6 W T h α β μ Q x = dualValues8 W T h α β μ Q x ∧
      ZD W T h α β μ Q x = ZD8 W T h α β μ Q x := by sorry

end MinimaxSLP.ObjSDP
