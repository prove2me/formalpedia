-- Prove2me | Theorems.Thm_GreedyAdvEq_Existence_proposition_7_4
-- name    : GreedyAdvEq.Existence.proposition_7_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:33:21.140987+00:00
-- url     : https://prove2.me/theorems/8c20fff6-98e2-4c49-8d4c-493cd247aeee
-- title:
--   Proposition 7.4, p. 30 — the polygonal path of Algorithm 1 is a (1/(1+δ))ε′-greedy path from y⁰ to y_LocalMax
-- statement:
--   Let $f$ be $C^2$ and $b$-bounded with $L$-Lipschitz Hessian on $\mathbb R^d\times\mathbb R^d$, and let $\nabla f$ be $L_2$-Lipschitz for the Euclidean norm on $\mathbb R^d\times\mathbb R^d$. Let $\delta>0$, $\mu_4\ge0$, let the eigen-oracle return unit eigenpairs $(\lambda,v)$ with $\lambda\ge\lambda_{\max}(\nabla_y^2f)-\mu_4$, let $\varepsilon'>0$, and let the step sizes satisfy
--   $$0<\mu_1\le\Big(1-\frac1{1+\delta}\Big)\frac1{2L_2},\qquad 0<\mu_3\le\Big(1-\frac1{1+\delta}\Big)\frac{\sqrt{\varepsilon'}}{2\sqrt L}.$$
--   Suppose Algorithm 1 with inputs $x, y^0, \varepsilon'$ terminates after $\ell_{\max}$ iterations, producing $y^0,y^1,\dots,y^{\ell_{\max}}$. Then the unit-speed path $\phi$ consisting of the segments $[y^\ell,y^{\ell+1}]$, parametrized by arc length on $[0,\tau]$ with $\tau=\sum_{\ell<\ell_{\max}}\|y^{\ell+1}-y^\ell\|$, is a $\frac1{1+\delta}\varepsilon'$-greedy path for $f(x,\cdot)$, with $\phi_0=y^0$ and $\phi_\tau=y_{\mathrm{LocalMax}}$.
--
--   This is what makes Algorithm 1's output a lower bound for the greedy max (Proposition 7.5): its endpoint is reachable by a greedy path.
--
--   **Formalization Note.** Greedy paths are read as in the Setting (directional second derivative $\dot\phi^\top\nabla_y^2f\,\dot\phi$). The step-size conditions are those the proof cites (p. 30), with $L_2$ a Lipschitz constant of $\nabla f$ given as a hypothesis (§7.1 sets $L_2=2b^{1/3}L^{2/3}$, footnote 4); they replace §7.1's printed hyperparameter formulas.
-- source:
--   Mangoubi, Vishnoi, Greedy Adversarial Equilibrium, arXiv:2006.12363v4, p. 30, Proposition 7.4 and its proof

import Mathlib
import Definitions.Def_GreedyAdvEq_Existence_Setting
import Definitions.Def_GreedyAdvEq_Existence_Algorithm1

namespace GreedyAdvEq.Existence

theorem proposition_7_4 (d : ℕ) (f : E d → E d → ℝ) (b L : ℝ) (hb : 0 < b) (hL : 0 < L)
    (hf : IsModel f b L) (L₂ : ℝ) (hL₂ : 0 < L₂)
    (hgrad : ∀ p q : WithLp 2 (E d × E d),
      ‖fderiv ℝ (joint f) p - fderiv ℝ (joint f) q‖ ≤ L₂ * ‖p - q‖)
    (Eig : E d → E d → ℝ × E d) (δ μ₁ μ₃ μ₄ : ℝ) (hδ : 0 < δ) (hμ₄ : 0 ≤ μ₄)
    (hEig : IsEigOracle f Eig μ₄) (x y0 : E d) (ε' : ℝ) (hε' : 0 < ε')
    (hμ₁ : 0 < μ₁) (hμ₁le : μ₁ ≤ (1 - 1 / (1 + δ)) * (1 / (2 * L₂)))
    (hμ₃ : 0 < μ₃) (hμ₃le : μ₃ ≤ (1 - 1 / (1 + δ)) * (Real.sqrt ε' / (2 * Real.sqrt L)))
    (hterm : Alg1Terminates f L Eig μ₁ μ₃ x y0 ε') :
    IsGreedyPath f L ((1 / (1 + δ)) * ε') x
        (knot (alg1Iter f L Eig μ₁ μ₃ x y0 ε') (alg1Len f L Eig μ₁ μ₃ x y0 ε'))
        (polygonalPath (alg1Iter f L Eig μ₁ μ₃ x y0 ε') (alg1Len f L Eig μ₁ μ₃ x y0 ε')) ∧
      polygonalPath (alg1Iter f L Eig μ₁ μ₃ x y0 ε') (alg1Len f L Eig μ₁ μ₃ x y0 ε') 0 = y0 ∧
      polygonalPath (alg1Iter f L Eig μ₁ μ₃ x y0 ε') (alg1Len f L Eig μ₁ μ₃ x y0 ε')
          (knot (alg1Iter f L Eig μ₁ μ₃ x y0 ε') (alg1Len f L Eig μ₁ μ₃ x y0 ε')) =
        alg1Out f L Eig μ₁ μ₃ x y0 ε' := by sorry

end GreedyAdvEq.Existence
