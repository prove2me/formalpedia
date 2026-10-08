-- Prove2me | Theorems.Thm_MinimaxSLP_RhsSDP_theorem_3_2
-- name    : MinimaxSLP.RhsSDP.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:15:59.138037+00:00
-- url     : https://prove2.me/theorems/5bcbd22f-c5d6-4de3-b21d-021935a59064
-- title:
--   Theorem 3.2, p. 589 — with random right-hand side and known dual extreme points, the minimax problem equals the SDP (14)
-- statement:
--   Consider the risk-averse minimax stochastic linear program with random right-hand side $\tilde h$ and constant objective $q$,
--   $$
--   Z=\min_{x\in X}\Big(c'x+\sup_{P\in\mathcal P}\mathbb E_P\big[\mathbb U(\mathcal Q(\tilde h,x))\big]\Big),
--   $$
--   where $X=\{x : Ax=b,\ x\ge 0\}$, $\mathcal Q(h,x)=\max\{(h-Tx)'p : W'p\le q\}$, $\mathbb U(t)=\max_k(\alpha_kt+\beta_k)$ and $\mathcal P$ is the class of distributions on $\mathbb R^r$ with mean $\mu$ and second-moment matrix $Q$. Assume:
--
--   1. $X$ is nonempty and bounded (Assumption 1);
--   2. $\alpha_k\ge 0$ for all $k$;
--   3. complete recourse, $\{Ww : w\ge 0\}=\mathbb R^r$ (Assumption 2);
--   4. $\{p : W'p\le q\}\neq\emptyset$ (Assumption 3 at the constant $q$);
--   5. $Q$ is symmetric and $Q\succ\mu\mu'$ (Assumption 4);
--   6. $p_1,\dots,p_N$ are the extreme points of $\{p : W'p\le q\}$ (Assumption 5).
--
--   Then the problem is equivalent to the semidefinite program
--   $$
--   \hat Z_{\rm SDP}=\min_{x,Y,y,y_0}\ c'x+Q\cdot Y+\mu'y+y_0\quad\text{s.t.}\quad\begin{pmatrix}Y & \tfrac12(y-\alpha_k p_i)\\ \tfrac12(y-\alpha_k p_i)' & y_0+\alpha_k p_i'Tx-\beta_k\end{pmatrix}\succeq 0\ \ \forall k,i,\qquad Ax=b,\ x\ge 0, \tag{14}
--   $$
--   in the following sense: for every $x\in X$ the worst-case expected disutility $\hat Z(x)$ equals the optimal value of (15); the infimum of $c'x+\hat Z(x)$ over $X$ and the infimum of the objective of (14) over its feasible set are the same real number $\hat Z_{\rm SDP}$; and $Z=\hat Z_{\rm SDP}$.
--
--   The theorem shows that, once the dual extreme points are available, the minimax problem — NP-hard in general (Theorem 3.1) — is a single semidefinite program, jointly in the first-stage decision and the dual multipliers.
--
--   **Formalization Note** The paper's "Assumption i" in the statement is read as Assumption 5 (see the proof's first line). The printed min are read as infima; both infima are asserted to be genuine (`IsGLB`), and attainment is not claimed. Assumptions 2 and 3 are used in the section-wise reading: complete recourse together with dual feasibility at the single constant $q$ (as printed, Assumption 3 "for all $q$" contradicts Assumption 2).
-- source:
--   Bertsimas, Doan, Natarajan & Teo, Models for Minimax Stochastic Linear Optimization Problems with Risk Aversion, Math. Oper. Res. 35(3), 2010, p. 589, Theorem 3.2, (14); proof pp. 589–590

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_WorstCaseVaR_KnownMoments_Basic
import Definitions.Def_MinimaxSLP_RhsSDP_Model

namespace MinimaxSLP.RhsSDP

open MeasureTheory Matrix

/-- Theorem 3.2, p. 589 (printed "Assumption i" read as Assumption 5). Under Assumption 1 (`X`
nonempty and bounded), `α_k ≥ 0`, complete recourse (Assumption 2), `{π : W′π ≤ q} ≠ ∅`
(Assumption 3 at the constant `q`), Assumption 4 and Assumption 5, the risk-averse minimax
problem `min_{x ∈ MinimaxSLP.ObjSDP.X} (c′x + Ẑ(x))` with random right-hand side is equivalent to the joint
semidefinite program (14): for every `x ∈ MinimaxSLP.ObjSDP.X`, `Ẑ(x)` equals the optimal value of (15); the
infimum of `c′x + Ẑ(x)` over `X` and the infimum of `c′x + Q · Y + μ′y + y₀` over the feasible
set of (14) are both the real number `Ẑ_SDP`; and `Z = Ẑ_SDP`. -/
theorem theorem_3_2 {m₁ n r d K N : ℕ} [NeZero K]
    (A : Matrix (Fin m₁) (Fin n) ℝ) (b : Fin m₁ → ℝ) (c : Fin n → ℝ)
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (q : Fin d → ℝ)
    (α β : Fin K → ℝ) (μ : Fin r → ℝ) (Q : Matrix (Fin r) (Fin r) ℝ)
    (ps : Fin N → Fin r → ℝ)
    (hA1 : (MinimaxSLP.ObjSDP.X A b).Nonempty ∧ Bornology.IsBounded (MinimaxSLP.ObjSDP.X A b))
    (hα : ∀ k, 0 ≤ α k)
    (hA2 : ∀ z : Fin r → ℝ, ∃ w : Fin d → ℝ, 0 ≤ w ∧ W *ᵥ w = z)
    (hA3 : ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (hQ : Q.IsSymm) (hA4 : (Q - Matrix.vecMulVec μ μ).PosDef)
    (hA5 : Set.range ps = Set.extremePoints ℝ {π : Fin r → ℝ | Wᵀ *ᵥ π ≤ q}) :
    (∀ x ∈ MinimaxSLP.ObjSDP.X A b, Zhat W T q α β μ Q x = ZhatD15 T α β ps μ Q x) ∧
      IsGLB (minimaxObj c W T q α β μ Q '' MinimaxSLP.ObjSDP.X A b) (ZhatSDP A b c T α β ps μ Q) ∧
      IsGLB (obj14 c μ Q '' feasible14 A b T α β ps) (ZhatSDP A b c T α β ps μ Q) ∧
      Zval A b c W T q α β μ Q = ZhatSDP A b c T α β ps μ Q := by sorry

end MinimaxSLP.RhsSDP
