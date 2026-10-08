-- Prove2me | Theorems.Thm_MinimaxSLP_RhsSDP_strong_duality
-- name    : MinimaxSLP.RhsSDP.strong_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:15:28.629119+00:00
-- url     : https://prove2.me/theorems/da9a8d78-2336-4dd8-b236-30afec2a8fc0
-- title:
--   §3.1, p. 588 — strong duality for (11)/(12): Ẑ(x) = Ẑ_D(x) under Q ≻ μμ′
-- statement:
--   Let $\alpha_k\ge 0$ for $k=1,\dots,K$, let $W,T,q$ satisfy complete recourse (Assumption 2) and $\{p : W'p\le q\}\neq\emptyset$ (Assumption 3 at the constant $q$), and let $Q$ be symmetric with $Q\succ\mu\mu'$ (Assumption 4). Then for every $x\in\mathbb R^n$ the worst-case expected disutility
--   $$
--   \hat Z(x)=\sup_{P\in\mathcal P}\mathbb E_P\big[\mathbb U(\mathcal Q(\tilde h,x))\big]
--   $$
--   is a finite real number which is the least upper bound of the expected disutilities over $\mathcal P$ and also the greatest lower bound of the objective values $Q\cdot Y+\mu'y+y_0$ of the dual (12); in particular
--   $$
--   \hat Z(x)=\hat Z_D(x).
--   $$
--
--   The paper states (12) as "the equivalent dual problem under the strong duality condition" and uses $\hat Z_D(x)=\hat Z(x)$ in the last line of the proof of Theorem 3.2.
--
--   **Formalization Note** "The strong duality condition" is read as Assumption 4, the interior condition $Q\succ\mu\mu'$ (written `(Q - vecMulVec μ μ).PosDef`). The `IsLUB`/`IsGLB` form rules out the junk values of real `sSup`/`sInf`; attainment of the dual minimum is not claimed.
-- source:
--   Bertsimas, Doan, Natarajan & Teo, Models for Minimax Stochastic Linear Optimization Problems with Risk Aversion, Math. Oper. Res. 35(3), 2010, p. 588, §3.1, (11)–(12); used on p. 590, proof of Theorem 3.2

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_WorstCaseVaR_KnownMoments_Basic
import Definitions.Def_MinimaxSLP_RhsSDP_Model

namespace MinimaxSLP.RhsSDP

open MeasureTheory Matrix

/-- Strong duality between the moment problem (11) and its dual (12), §3.1, p. 588 ("under the
strong duality condition, the equivalent dual problem is (12)"; used as "from the strong duality
assumption, we have `Ẑ_D(x) = Ẑ(x)`", p. 590). The strong duality condition is read as
Assumption 4, `Q ≻ μμ′`. Under `α_k ≥ 0`, complete recourse (Assumption 2), `{π : W′π ≤ q} ≠ ∅`
(Assumption 3 at the constant `q`) and Assumption 4, for every `x` the real number `Ẑ(x)` is the
least upper bound of `{E_P[𝕌(𝒬(h̃, x))] : P ∈ 𝒫}` and the greatest lower bound of the
objective values `Q · Y + μ′y + y₀` of (12), and `Ẑ(x) = Ẑ_D(x)`. -/
theorem strong_duality {r d n K : ℕ} [NeZero K]
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (q : Fin d → ℝ)
    (α β : Fin K → ℝ) (μ : Fin r → ℝ) (Q : Matrix (Fin r) (Fin r) ℝ)
    (hα : ∀ k, 0 ≤ α k)
    (hA2 : ∀ z : Fin r → ℝ, ∃ w : Fin d → ℝ, 0 ≤ w ∧ W *ᵥ w = z)
    (hA3 : ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (hQ : Q.IsSymm) (hA4 : (Q - Matrix.vecMulVec μ μ).PosDef)
    (x : Fin n → ℝ) :
    IsLUB (primalValues W T q α β μ Q x) (Zhat W T q α β μ Q x) ∧
      IsGLB (dualObj μ Q '' dualFeasible12 W T q α β x) (Zhat W T q α β μ Q x) ∧
      Zhat W T q α β μ Q x = ZhatD W T q α β μ Q x := by sorry

end MinimaxSLP.RhsSDP
