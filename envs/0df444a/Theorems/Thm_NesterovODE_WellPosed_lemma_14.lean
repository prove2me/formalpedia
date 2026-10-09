-- Prove2me | Theorems.Thm_NesterovODE_WellPosed_lemma_14
-- name    : NesterovODE.WellPosed.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:42:06.994501+00:00
-- url     : https://prove2.me/theorems/8e403855-c846-4420-83f6-cea2ae45067a
-- title:
--   Lemma 14, p. 28 — existence for the singular ODE
-- statement:
--   For every $f\in\mathcal F_\infty=\bigcup_{L>0}\mathcal F_L$ and every $x_0\in\mathbb R^n$, there exists a global solution $X$ of (3) with $X(0)=x_0$, $\dot X(0)=0$, and
--   $$
--   X\in C^2((0,\infty);\mathbb R^n)\cap C^1([0,\infty);\mathbb R^n).
--   $$
--   This supplies the existence half of Theorem 1.
--
--   **Formalization Note** A velocity function records $\dot X$, with a one-sided derivative and continuity at zero. Negative-time values of the functions are unrestricted.
-- source:
--   Su, Boyd, Candès, A Differential Equation for Modeling Nesterov's Accelerated Gradient Method, arXiv:1503.01243v2, p. 28, Lemma 14

import Mathlib
import Definitions.Def_NesterovODE_WellPosed_Setting

namespace NesterovODE.WellPosed

/-- Lemma 14, p. 28: existence for the singular ODE. -/
theorem lemma_14 {n : ℕ} (f : E n → ℝ) (x₀ : E n)
    (hf : ∃ L : NNReal, IsFL f L) :
    ∃ X V : ℝ → E n, IsSolution f 3 x₀ X V := by sorry

end NesterovODE.WellPosed
