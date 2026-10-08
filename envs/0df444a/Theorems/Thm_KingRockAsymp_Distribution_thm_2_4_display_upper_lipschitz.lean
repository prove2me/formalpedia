-- Prove2me | Theorems.Thm_KingRockAsymp_Distribution_thm_2_4_display_upper_lipschitz
-- name    : KingRockAsymp.Distribution.thm_2_4_display_upper_lipschitz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:58:10.575153+00:00
-- url     : https://prove2.me/theorems/cb174ab6-5586-48a5-8ab5-8b6d882c8110
-- title:
--   Proof of Theorem 2.4, display (p. 7) — upper-Lipschitz inverse (cited from [12], Prop. 2.1)
-- statement:
--   Let $F : \mathbb R^n \rightrightarrows \mathbb R^m$ be a multifunction with $0 \in F(x^*)$, and suppose that the contingent derivative of $F^{-1}$ at $(0,x^*)$ satisfies
--   $$DF^{-1}(0|x^*)(0) = \{0\}.$$
--   Then there are a neighborhood $U$ of $x^*$ and a constant $\lambda \ge 0$ such that
--   $$U \cap F^{-1}(y) \subseteq x^* + \lambda |y| B$$
--   for all $y$ sufficiently close to $0$ in $\mathbb R^m$, where $B$ is the closed unit ball of $\mathbb R^n$.
--
--   This is the upper-Lipschitz property of $F^{-1}$ at $(0, x^*)$. The paper cites it from King and Rockafellar's *Sensitivity analysis for nonsmooth generalized equations* ([12], Proposition 2.1) in the proof of Theorem 2.4; it turns the single-valuedness of the contingent derivative at $0$ into bounds in probability on solutions.
--
--   **Formalization Note** $DF^{-1}(0|x^*)$ is the contingent derivative (2.2) of the inverse multifunction. "For all $y$ sufficiently close to $0$" is `∀ᶠ y in 𝓝 0`; $U$ and $\lambda$ are chosen before $y$.
-- source:
--   King & Rockafellar, Asymptotic Theory for Solutions in Statistical Estimation and Stochastic Programming, Math. Oper. Res. 18(1) (1993), proof of Theorem 2.4, display, p. 7 (authors' manuscript pagination); cited from [12], Proposition 2.1

import Mathlib
import Definitions.Def_KingRockAsymp_Distribution_Basic

namespace KingRockAsymp.Distribution

open Set Filter Topology Metric MeasureTheory ProbabilityTheory

theorem thm_2_4_display_upper_lipschitz {n m : ℕ} (F : Rn n → Set (Rn m)) (x₀ : Rn n)
    (h0 : (0 : Rn m) ∈ F x₀)
    (hD : contingentDeriv (svInv F) 0 x₀ 0 = {0}) :
    ∃ U ∈ 𝓝 x₀, ∃ lam : ℝ, 0 ≤ lam ∧
      ∀ᶠ y in 𝓝 (0 : Rn m), U ∩ svInv F y ⊆ closedBall x₀ (lam * ‖y‖) := by sorry

end KingRockAsymp.Distribution
