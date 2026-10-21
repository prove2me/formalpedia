-- Prove2me | Theorems.Thm_LiqProvision_Oligopoly_proposition_C_4
-- name    : LiqProvision.Oligopoly.proposition_C_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:40:52.190647+00:00
-- url     : https://prove2.me/theorems/8c599dfb-f711-4d7d-9a89-cce4dbc90edd
-- title:
--   Proposition C.4, p. 33 — global solutions between lower and upper solutions of y′ = α(x, y) on a half-line
-- statement:
--   Let $I=[0,\infty)$ or $I=(-\infty,0]$. Let $v\le w$ be differentiable on $I$, put $\Gamma=\{(x,y): x\in I,\ v(x)\le y\le w(x)\}$, and let $\alpha:\Gamma\to\mathbb R$ be continuous with a partial derivative $\alpha_y$ that is continuous on $\Gamma$ up to the boundary. Suppose either $I=[0,\infty)$ and
--   $$w'(x)-\alpha(x,w(x))\le0\le v'(x)-\alpha(x,v(x))\qquad(x\in I),\qquad (C.3)$$
--   or $I=(-\infty,0]$ and
--   $$v'(x)-\alpha(x,v(x))\le0\le w'(x)-\alpha(x,w(x))\qquad(x\in I).\qquad(C.4)$$
--   Then the differential equation $y'(x)=\alpha(x,y(x))$ has a solution $\varphi$ on all of $I$ with $v\le\varphi\le w$.
--
--   It is the existence tool for the ODE (3.8) on each half-line.
--
--   **Formalization Note.** Generic statement. $\alpha$ and $\alpha_y$ are functions on $\mathbb R^2$ of which only the values on $\Gamma$ matter; $\alpha_y(x,y)$ is required to be the derivative of $y\mapsto\alpha(x,y)$ within $[v(x),w(x)]$. Derivatives of $v,w,\varphi$ at the endpoint $0$ are one-sided (within $I$). The inequality directions are exactly those of the page.
-- source:
--   Herdegen, Muhle-Karbe and Stebegg, Liquidity Provision with Adverse Selection and Inventory Costs, arXiv:2107.12094v1, p. 33, Proposition C.4, (C.2)–(C.4)

import Mathlib

namespace LiqProvision.Oligopoly
theorem proposition_C_4 (I : Set ℝ) (v w : ℝ → ℝ) (α αy : ℝ → ℝ → ℝ)
    (hv : DifferentiableOn ℝ v I) (hw : DifferentiableOn ℝ w I) (hvw : ∀ x ∈ I, v x ≤ w x)
    (hα : ContinuousOn (Function.uncurry α) {q : ℝ × ℝ | q.1 ∈ I ∧ v q.1 ≤ q.2 ∧ q.2 ≤ w q.1})
    (hαy : ContinuousOn (Function.uncurry αy) {q : ℝ × ℝ | q.1 ∈ I ∧ v q.1 ≤ q.2 ∧ q.2 ≤ w q.1})
    (hαy' : ∀ x ∈ I, ∀ y, v x ≤ y → y ≤ w x →
      HasDerivWithinAt (α x) (αy x y) (Set.Icc (v x) (w x)) y)
    (hcase : (I = Set.Ici 0 ∧ ∀ x ∈ I,
        derivWithin w I x - α x (w x) ≤ 0 ∧ 0 ≤ derivWithin v I x - α x (v x)) ∨
      (I = Set.Iic 0 ∧ ∀ x ∈ I,
        derivWithin v I x - α x (v x) ≤ 0 ∧ 0 ≤ derivWithin w I x - α x (w x))) :
    ∃ φ : ℝ → ℝ, (∀ x ∈ I, HasDerivWithinAt φ (α x (φ x)) I x) ∧
      ∀ x ∈ I, v x ≤ φ x ∧ φ x ≤ w x := by sorry
end LiqProvision.Oligopoly
