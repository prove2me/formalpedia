-- Prove2me | Theorems.Thm_GreedyAdvEq_Existence_proposition_7_5
-- name    : GreedyAdvEq.Existence.proposition_7_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:32:54.446424+00:00
-- url     : https://prove2.me/theorems/e19175de-f719-4c1a-8cde-159250ca350f
-- title:
--   Proposition 7.5, p. 30, (52) — Algorithm 1 terminates and h_ε○(x, y) ≤ g_ε○(x, y) for all x, y and every ε○ > 0 meeting the step-size bounds
-- statement:
--   Let $f$ be $C^2$ and $b$-bounded with $L$-Lipschitz Hessian, let $\nabla f$ be $L_2$-Lipschitz, let $\delta>0$, $\mu_4\ge0$, let the eigen-oracle be as in Algorithm 1, and let $0<\mu_1\le(1-\frac1{1+\delta})\frac1{2L_2}$ and $\mu_3>0$. Then for all $x,y\in\mathbb R^d$ and every $\varepsilon^\circ>0$ with
--   $$\mu_3\le\Big(1-\frac1{1+\delta}\Big)\frac{\sqrt{(1+\delta)\varepsilon^\circ}}{2\sqrt L},$$
--   Algorithm 1 with inputs $x$, $y^0=y$, $\varepsilon'=(1+\delta)\varepsilon^\circ$ terminates, and
--   $$h_{\varepsilon^\circ}(x,y)\le g_{\varepsilon^\circ}(x,y). \tag{52}$$
--
--   The computable function $h$ is thus a lower bound for the greedy max $g$, which in general cannot be computed; this is hypothesis (32) of Lemma 7.3.
--
--   **Formalization Note.** The page states (52) "for all $\varepsilon^\circ>0$" with fixed hyperparameters, but its proof applies Proposition 7.4 at $\varepsilon'=(1+\delta)\varepsilon^\circ$, whose step-size bound on $\mu_3$ depends on $\varepsilon'$; the statement quantifies over the $\varepsilon^\circ$ for which that bound holds. Termination of Algorithm 1 (shown in the proof of Lemma 7.1) is part of the conclusion, so the junk output of a non-terminating run plays no role.
-- source:
--   Mangoubi, Vishnoi, Greedy Adversarial Equilibrium, arXiv:2006.12363v4, p. 30, Proposition 7.5, (52); termination from the proof of Lemma 7.1, p. 24

import Mathlib
import Definitions.Def_GreedyAdvEq_Existence_Setting
import Definitions.Def_GreedyAdvEq_Existence_Algorithm1

namespace GreedyAdvEq.Existence

theorem proposition_7_5 (d : ℕ) (f : E d → E d → ℝ) (b L : ℝ) (hb : 0 < b) (hL : 0 < L)
    (hf : IsModel f b L) (L₂ : ℝ) (hL₂ : 0 < L₂)
    (hgrad : ∀ p q : WithLp 2 (E d × E d),
      ‖fderiv ℝ (joint f) p - fderiv ℝ (joint f) q‖ ≤ L₂ * ‖p - q‖)
    (Eig : E d → E d → ℝ × E d) (δ μ₁ μ₃ μ₄ : ℝ) (hδ : 0 < δ) (hμ₄ : 0 ≤ μ₄)
    (hEig : IsEigOracle f Eig μ₄)
    (hμ₁ : 0 < μ₁) (hμ₁le : μ₁ ≤ (1 - 1 / (1 + δ)) * (1 / (2 * L₂))) (hμ₃ : 0 < μ₃) :
    ∀ x y : E d, ∀ ε : ℝ, 0 < ε →
      μ₃ ≤ (1 - 1 / (1 + δ)) * (Real.sqrt ((1 + δ) * ε) / (2 * Real.sqrt L)) →
      Alg1Terminates f L Eig μ₁ μ₃ x y ((1 + δ) * ε) ∧
        hEps f L Eig δ μ₁ μ₃ ε x y ≤ greedyMax f L ε x y := by sorry

end GreedyAdvEq.Existence
