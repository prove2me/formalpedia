-- Prove2me | Theorems.Thm_MinimaxSLP_ObjExtremal_strong_duality
-- name    : MinimaxSLP.ObjExtremal.strong_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:15:11.370428+00:00
-- url     : https://prove2.me/theorems/5ed5e328-fc8e-4cd3-92a4-3c1be3a86b49
-- title:
--   §2.1, p. 583 — strong duality $Z(x)=Z_D(x)$ between the moment problem (5) and its dual (6)
-- statement:
--   Let $x\in X$, assume $X(x)\neq\emptyset$, Assumption 3 ($\{p : W'p\le q\}\neq\emptyset$ for all $q\in\mathbb R^d$), $\alpha_k\ge0$ for all $k$, and Assumption 4: $Q$ is symmetric and the covariance matrix $Q-\mu\mu'$ is positive definite. Then the moment problem
--   $$
--   Z(x)=\sup_{P\in\mathcal P}\mathbb E_P\big[\mathbb U(\mathcal Q(\tilde q,x))\big]
--   $$
--   and its dual (6),
--   $$
--   Z_D(x)=\min_{Y,y,y_0}\ Q\cdot Y+\mu'y+y_0\quad\text{s.t.}\quad q'Yq+q'y+y_0\ge\mathbb U(\mathcal Q(q,x))\ \ \forall q\in\mathbb R^d,
--   $$
--   have the same finite optimal value:
--
--   1. the set of values $\mathbb E_P[\mathbb U(\mathcal Q(\tilde q,x))]$, $P\in\mathcal P$, is nonempty and bounded above, with supremum $Z(x)$;
--   2. the set of objective values of feasible points of (6) is nonempty and bounded below, with infimum $Z_D(x)$;
--   3. $Z(x)=Z_D(x)$.
--
--   The paper obtains this from the strong duality theory of the moment problem (Isii), the interior condition being Assumption 4. It is the step $Z(x)=Z_D(x)$ in the final chain of the proof of Theorem 2.2.
--
--   **Formalization Note** The interior condition "the moment vector lies in the interior of the set of feasible moment vectors" is read as Assumption 4. The printed min of (6) is read as an infimum; attainment is not claimed. The same statement appears in the companion mission on Theorem 2.1.
-- source:
--   Bertsimas, Doan, Natarajan & Teo, Models for Minimax Stochastic Linear Optimization Problems with Risk Aversion, Math. Oper. Res. 35(3), 2010, p. 583, §2.1 (strong duality, citing Isii)

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_MinimaxSLP_ObjExtremal_Model

open MeasureTheory Matrix Filter Topology

namespace MinimaxSLP.ObjExtremal

/-- §2.1 (p. 583): strong duality `Z(x) = Z_D(x)` between the moment problem (5) and its dual
(6), under Assumption 4 (`Q − μμ′ ≻ 0`, the interior condition). Both optimal values are genuine:
the primal values are bounded above with least upper bound `Z(x)`, the dual values bounded below
with greatest lower bound `Z_D(x)`. -/
theorem strong_duality {m₁ n r d K : ℕ} [NeZero K]
    (A : Matrix (Fin m₁) (Fin n) ℝ) (b : Fin m₁ → ℝ)
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (α β : Fin K → ℝ) (hα : ∀ k, 0 ≤ α k)
    (μ : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.IsSymm) (hA4 : (Q - Matrix.vecMulVec μ μ).PosDef)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (hx : x ∈ MinimaxSLP.ObjSDP.X A b) (hrec : (MinimaxSLP.ObjSDP.recourseSet W T h x).Nonempty) :
    IsLUB (MinimaxSLP.ObjSDP.primalValues W T h α β μ Q x) (MinimaxSLP.ObjSDP.Zx W T h α β μ Q x) ∧
    IsGLB (MinimaxSLP.ObjSDP.dualValues6 W T h α β μ Q x) (MinimaxSLP.ObjSDP.ZD W T h α β μ Q x) ∧
    MinimaxSLP.ObjSDP.Zx W T h α β μ Q x = MinimaxSLP.ObjSDP.ZD W T h α β μ Q x := by sorry

end MinimaxSLP.ObjExtremal
