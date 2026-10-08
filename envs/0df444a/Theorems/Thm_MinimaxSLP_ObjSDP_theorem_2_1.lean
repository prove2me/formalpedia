-- Prove2me | Theorems.Thm_MinimaxSLP_ObjSDP_theorem_2_1
-- name    : MinimaxSLP.ObjSDP.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:09:49.655446+00:00
-- url     : https://prove2.me/theorems/828f9c12-8f1c-468a-ae4c-127fc1f7dfe0
-- title:
--   Theorem 2.1, p. 583 — with random objective, the risk-averse minimax problem (2) equals the semidefinite program (7)
-- statement:
--   Consider the two-stage minimax problem (2) with random objective $\tilde q\in\mathbb R^d$ and constant right-hand side $h$:
--   $$
--   Z=\min_{x\in X}\Big(c'x+\sup_{P\in\mathcal P}\mathbb E_P\big[\mathbb U(\mathcal Q(\tilde q,x))\big]\Big),
--   $$
--   where $X=\{x : Ax=b,\ x\ge 0\}$, $\mathcal Q(q,x)=\min\{q'w : Ww=h-Tx,\ w\ge 0\}$, $\mathbb U(t)=\max_{k=1,\dots,K}(\alpha_k t+\beta_k)$ with $\alpha_k\ge 0$, and $\mathcal P$ is the class of distributions with mean $\mu$ and second-moment matrix $\mathbb E_P[\tilde q\tilde q']=Q$. Assume:
--
--   1. $X$ is nonempty and bounded (Assumption 1);
--   2. $X(x)=\{w : Ww=h-Tx,\ w\ge 0\}\neq\emptyset$ for every $x\in X$;
--   3. $\{\pi\in\mathbb R^r : W'\pi\le q\}\neq\emptyset$ for every $q\in\mathbb R^d$ (Assumption 3);
--   4. $Q$ is symmetric and $Q-\mu\mu'\succ 0$ (Assumption 4).
--
--   Then $Z$ equals the optimal value of the semidefinite program
--   $$
--   Z_{\mathrm{SDP}}=\min_{x,Y,y,y_0,w_k}\ c'x+Q\cdot Y+\mu'y+y_0\quad\text{s.t.}\quad \begin{pmatrix}Y & \tfrac12(y-\alpha_k w_k)\\ \tfrac12(y-\alpha_k w_k)' & y_0-\beta_k\end{pmatrix}\succeq 0,\ \ Ww_k+Tx=h,\ \ w_k\ge 0\ \ (k=1,\dots,K),\quad Ax=b,\ x\ge 0, \tag{7}
--   $$
--   both values being finite (the objective values of (2) are bounded below with greatest lower bound $Z$, those of (7) with greatest lower bound $Z_{\mathrm{SDP}}$), and $Z=Z_{\mathrm{SDP}}$. Moreover, for every $x\in X$ the worst-case expected disutility $Z(x)$ equals the optimal value of the semidefinite program (8) obtained from (7) by fixing $x$.
--
--   The theorem reduces a minimax stochastic linear program over an infinite-dimensional set of distributions to a single semidefinite program whose size is polynomial in $n$, $d$, $r$ and $K$.
--
--   **Formalization Note** Assumption 2 (complete recourse) and Assumption 3 for all $q$, as printed on p. 582, cannot both hold when $r\ge 1$; the proof of Theorem 2.1 uses Assumption 3 for all $q$ and only the nonemptiness of $X(x)$ for $x\in X$, which replaces Assumption 2 here. The printed minima are read as infima; attainment is not claimed. Distributions are measures with finite second moments rather than densities. The per-$x$ identity $Z(x)=Z_{(8)}(x)$ is the content of the last line of the paper's proof ("$Z_D(x)=Z(x)$ for all $x\in X$").
-- source:
--   Bertsimas, Doan, Natarajan & Teo, Models for Minimax Stochastic Linear Optimization Problems with Risk Aversion, Math. Oper. Res. 35(3), 2010, p. 583, Theorem 2.1 (proof pp. 583–584; Assumptions 1–4, p. 582)

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_MinimaxSLP_ObjSDP_Model

open MeasureTheory Matrix

namespace MinimaxSLP.ObjSDP

/-- Theorem 2.1 (p. 583): under Assumption 1, relatively complete recourse on `X` (in place of
Assumption 2, see the mission notes), Assumption 3 for all `q` and Assumption 4, the risk-averse
minimax problem (2) with random objective `q̃` and constant right-hand side `h` is equivalent to
the semidefinite program (7): both optimal values are genuine infima and `Z = Z_SDP`; moreover,
for every `x ∈ X`, `Z(x)` equals the optimal value of (8). -/
theorem theorem_2_1 {m₁ n r d K : ℕ} [NeZero K]
    (A : Matrix (Fin m₁) (Fin n) ℝ) (b : Fin m₁ → ℝ) (c : Fin n → ℝ)
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (α β : Fin K → ℝ) (hα : ∀ k, 0 ≤ α k)
    (μ : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ)
    (hA1 : (X A b).Nonempty ∧ Bornology.IsBounded (X A b))
    (hrec : ∀ x ∈ X A b, (recourseSet W T h x).Nonempty)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (hQ : Q.IsSymm) (hA4 : (Q - Matrix.vecMulVec μ μ).PosDef) :
    IsGLB (firstStageValues A b c W T h α β μ Q) (Z A b c W T h α β μ Q) ∧
    IsGLB (values7 A b c W T h α β μ Q) (ZSDP A b c W T h α β μ Q) ∧
    Z A b c W T h α β μ Q = ZSDP A b c W T h α β μ Q ∧
    ∀ x ∈ X A b, Zx W T h α β μ Q x = ZD8 W T h α β μ Q x := by sorry

end MinimaxSLP.ObjSDP
