-- Prove2me | Theorems.Thm_NesterovODE_WellPosed_theorem_1
-- name    : NesterovODE.WellPosed.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:41:21.209527+00:00
-- url     : https://prove2.me/theorems/bfd1448b-084a-4cd4-bde0-e634c9c185e3
-- title:
--   Theorem 1, p. 6 — unique global solution of the singular ODE
-- statement:
--   For any $f\in\mathcal F_\infty=\bigcup_{L>0}\mathcal F_L$ and $x_0\in\mathbb R^n$, the singular ODE
--   $$
--   \ddot X(t)+\frac3t\dot X(t)+\nabla f(X(t))=0\quad(t>0),
--   \qquad X(0)=x_0,\quad\dot X(0)=0
--   $$
--   has a global solution in $C^2((0,\infty);\mathbb R^n)\cap C^1([0,\infty);\mathbb R^n)$. Any two such solutions agree on $[0,\infty)$.
--
--   This establishes that the continuous-time model used elsewhere in the paper is well defined from the prescribed initial data.
--
--   **Formalization Note** The $\mathcal F_L$ class includes convexity, continuous differentiability, a positive $L$, and a globally $L$-Lipschitz gradient. The ODE is imposed only at $t>0$, and uniqueness is equality on the nonnegative half-line; representatives on negative time are unconstrained.
-- source:
--   Su, Boyd, Candès, A Differential Equation for Modeling Nesterov's Accelerated Gradient Method, arXiv:1503.01243v2, p. 6, Theorem 1

import Mathlib
import Definitions.Def_NesterovODE_WellPosed_Setting

namespace NesterovODE.WellPosed

/-- Theorem 1, p. 6: existence and uniqueness on [0,∞) for the singular ODE. -/
theorem theorem_1 {n : ℕ} (f : E n → ℝ) (x₀ : E n)
    (hf : ∃ L : NNReal, IsFL f L) :
    (∃ X V : ℝ → E n, IsSolution f 3 x₀ X V) ∧
    (∀ X V Y W : ℝ → E n,
      IsSolution f 3 x₀ X V → IsSolution f 3 x₀ Y W →
      Set.EqOn X Y (Set.Ici 0)) := by sorry

end NesterovODE.WellPosed
