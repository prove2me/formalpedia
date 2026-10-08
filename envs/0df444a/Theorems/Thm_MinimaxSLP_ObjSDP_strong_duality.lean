-- Prove2me | Theorems.Thm_MinimaxSLP_ObjSDP_strong_duality
-- name    : MinimaxSLP.ObjSDP.strong_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:09:04.333215+00:00
-- url     : https://prove2.me/theorems/f1f8b44e-efc1-4a7c-80db-cfa843c644fa
-- title:
--   §2.1, p. 583 — strong duality $Z(x) = Z_D(x)$ under Assumption 4
-- statement:
--   Let $W$, $T$, $h$, $\mathbb U$ (with $\alpha_k\ge 0$) be as in the model, let $Q$ be symmetric, and assume Assumption 3 ($\{\pi : W'\pi\le q\}\neq\emptyset$ for every $q\in\mathbb R^d$) and Assumption 4,
--   $$
--   Q-\mu\mu'\succ 0 .
--   $$
--   Let $x$ have a nonempty recourse set $X(x)$. Then the set of values $\{\mathbb E_P[\mathbb U(\mathcal Q(\tilde q,x))] : P\in\mathcal P\}$ is bounded above with least upper bound $Z(x)$, the set of objective values of the dual (6) is bounded below with greatest lower bound $Z_D(x)$, and
--   $$
--   Z(x)=Z_D(x).
--   $$
--
--   The paper obtains this from the general strong duality theory of the moment problem (Isii): the moment vector lies in the interior of the set of feasible moment vectors because the covariance $Q-\mu\mu'$ is positive definite. It is what allows the inner supremum over distributions in problem (2) to be replaced by a minimization.
--
--   **Formalization Note** The paper's interior condition is read as Assumption 4. The statement is for this integrand $\mathbb U(\mathcal Q(\cdot,x))$, not for a general function. Distributions are measures with finite second moments.
-- source:
--   Bertsimas, Doan, Natarajan & Teo, Models for Minimax Stochastic Linear Optimization Problems with Risk Aversion, Math. Oper. Res. 35(3), 2010, p. 583, §2.1 (strong duality, citing Isii [15]; Assumption 4, p. 582)

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_MinimaxSLP_ObjSDP_Model

open MeasureTheory Matrix

namespace MinimaxSLP.ObjSDP

/-- §2.1 (p. 583): strong duality `Z(x) = Z_D(x)` between the moment problem (5) and its dual
(6), under Assumption 4 (`Q − μμ′ ≻ 0`, read as the interior condition). Both optimal values are
genuine: the primal values are bounded above with least upper bound `Z(x)`, the dual values are
bounded below with greatest lower bound `Z_D(x)`. -/
theorem strong_duality {n r d K : ℕ} [NeZero K]
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (α β : Fin K → ℝ) (hα : ∀ k, 0 ≤ α k)
    (μ : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.IsSymm) (hA4 : (Q - Matrix.vecMulVec μ μ).PosDef)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (hrec : (recourseSet W T h x).Nonempty) :
    IsLUB (primalValues W T h α β μ Q x) (Zx W T h α β μ Q x) ∧
    IsGLB (dualValues6 W T h α β μ Q x) (ZD W T h α β μ Q x) ∧
    Zx W T h α β μ Q x = ZD W T h α β μ Q x := by sorry

end MinimaxSLP.ObjSDP
