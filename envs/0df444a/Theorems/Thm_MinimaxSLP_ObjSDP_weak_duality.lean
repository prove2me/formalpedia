-- Prove2me | Theorems.Thm_MinimaxSLP_ObjSDP_weak_duality
-- name    : MinimaxSLP.ObjSDP.weak_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:09:00.996988+00:00
-- url     : https://prove2.me/theorems/ffd82195-2596-4704-af94-67ed1df5848e
-- title:
--   §2.1, p. 583 — weak duality $Z(x) \le Z_D(x)$ for the moment problem (5) and its dual (6)
-- statement:
--   Let $W\in\mathbb R^{r\times d}$, $T\in\mathbb R^{r\times n}$, $h\in\mathbb R^r$, and let $\mathbb U(t)=\max_k(\alpha_k t+\beta_k)$ with $\alpha_k\ge 0$ for all $k$. Assume that $\{\pi\in\mathbb R^r : W'\pi\le q\}\neq\emptyset$ for every $q\in\mathbb R^d$ (Assumption 3), and let $x\in\mathbb R^n$ have a nonempty recourse set $X(x)$. Then for every distribution $P$ in the moment class $\mathcal P$ of (4) (mean $\mu$, second-moment matrix $Q$) and every feasible point $(Y,y,y_0)$ of the dual (6),
--   $$
--   \mathbb E_P\big[\mathbb U(\mathcal Q(\tilde q,x))\big]\ \le\ Q\cdot Y+\mu'y+y_0 .
--   $$
--   Taking the supremum over $P$ and the infimum over $(Y,y,y_0)$ gives $Z(x)\le Z_D(x)$.
--
--   This is the easy half of the duality between the moment problem and its semi-infinite dual; it bounds the worst-case expected disutility by any feasible dual objective.
--
--   **Formalization Note** The inequality is stated pointwise, between every element of the set of primal values and every element of the set of dual values, so that it does not depend on how `sSup`/`sInf` treat empty or unbounded sets. Integrability of $\mathbb U(\mathcal Q(\cdot,x))$ under $P$ is part of what has to be proved, not a hypothesis.
-- source:
--   Bertsimas, Doan, Natarajan & Teo, Models for Minimax Stochastic Linear Optimization Problems with Risk Aversion, Math. Oper. Res. 35(3), 2010, p. 583, §2.1 (weak duality for (5)–(6))

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_MinimaxSLP_ObjSDP_Model

open MeasureTheory Matrix

namespace MinimaxSLP.ObjSDP

/-- §2.1 (p. 583): weak duality `Z(x) ≤ Z_D(x)` between the moment problem (5) and its dual (6),
in pointwise form: for every distribution `P` in the moment class (4) and every feasible point
`(Y, y, y₀)` of (6), `E_P[𝕌(𝒬(q̃, x))] ≤ Q · Y + μ′y + y₀`. -/
theorem weak_duality {n r d K : ℕ} [NeZero K]
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (α β : Fin K → ℝ) (hα : ∀ k, 0 ≤ α k)
    (μ : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (hrec : (recourseSet W T h x).Nonempty) :
    ∀ v ∈ primalValues W T h α β μ Q x, ∀ u ∈ dualValues6 W T h α β μ Q x, v ≤ u := by sorry

end MinimaxSLP.ObjSDP
