-- Prove2me | Theorems.Thm_FullyCoupledSDE_Poisson_theorem_2_1_eta_zero
-- name    : FullyCoupledSDE.Poisson.theorem_2_1_eta_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:27:01.71535+00:00
-- url     : https://prove2.me/theorems/f8d7dba7-3eeb-4bda-a360-3e563c68960d
-- title:
--   Theorem 2.1, case η = 0, p. 1210 — unique centered solution u ∈ C^{2+δ,0}_p of L0u = f with the estimates (2.1)–(2.2)
-- statement:
--   Let $a,b$ satisfy (Aσ) and (Ab) and lie in $C^{\delta,0}_b$ with $0<\delta\le1$, and let $(\mu^y)_y$ be the invariant family of $\mathscr L_0$. Let $f\in C^{\delta,0}_p$ be centered, $\int f(x,y)\,\mu^y(dx)=0$ for all $y$. Then:
--
--   1. there is a centered $u\in C^{2+\delta,0}_p$ with $\mathscr L_0(x,y)u(x,y)=f(x,y)$ for all $x,y$, and constants $C_0,m>0$ such that for all $x,x_1,x_2,y$
--   $$|u(x,y)|+|\nabla_xu(x,y)|+|\nabla^2_xu(x,y)|\le C_0(1+|x|^m),\qquad(2.1)$$
--   $$|\nabla^2_xu(x_1,y)-\nabla^2_xu(x_2,y)|\le C_0(|x_1-x_2|^\delta\wedge1)(1+|x_1|^m+|x_2|^m);\qquad(2.2)$$
--   2. any two centered solutions of (1.1) in $C^{2+\delta,0}_p$ are equal.
--
--   This is the optimal $x$-regularity part of Theorem 2.1 (Steps 1–2 of its proof). It is the base case from which the $y$-regularity for $\eta>0$ is derived.
--
--   **Formalization Note** The constants $C_0,m$ exist for each fixed $(a,b,f)$; the paper's claim that they depend only on $d_1,d_2$, $\|a\|_{C^{\delta,0}_b}$, $\|b\|_{C^{\delta,0}_b}$, $[f]_{C^{\delta,0}_p}$ is not posed, because it is false as printed ($[f]_{C^{\delta,0}_p}$ only sees the unit ball, and $\lambda$ and the rate in (Ab) are missing). Uniqueness is stated for the whole class, not only among solutions satisfying (2.1). Gradient and Hessian norms are operator norms.
-- source:
--   Röckner & Xie, Diffusion approximation for fully coupled SDEs, Ann. Probab. 49 (2021), p. 1210, Theorem 2.1 (i) (Case η = 0), (2.1)–(2.2); proof Steps 1–2, pp. 1217–1219

import Mathlib
import Definitions.Def_FullyCoupledSDE_Poisson_Setting

namespace FullyCoupledSDE.Poisson

open MeasureTheory

/-- Theorem 2.1, case `η = 0` (p. 1210; Steps 1–2, pp. 1217–1219). Under (Aσ), (Ab) and
`a, b ∈ C^{δ,0}_b`, for every centered `f ∈ C^{δ,0}_p` the equation (1.1) has a centered solution
`u ∈ C^{2+δ,0}_p` satisfying (2.1) and (2.2), and it is unique among centered solutions in
`C^{2+δ,0}_p`. -/
theorem theorem_2_1_eta_zero {d1 d2 : ℕ} (hd1 : 1 ≤ d1) (hd2 : 1 ≤ d2)
    (a : E d1 → E d2 → Matrix (Fin d1) (Fin d1) ℝ) (b : E d1 → E d2 → E d1)
    (μ : E d2 → Measure (E d1)) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hσ : AssumpSigma a) (hb : AssumpB b) (ha : CbMat δ 0 a) (hbb : Cb δ 0 b)
    (hμ : IsInvariantFamily a b μ)
    (f : E d1 → E d2 → ℝ) (hf : Cp δ 0 f) (hfc : Centered μ f) :
    (∃ u : E d1 → E d2 → ℝ, Cp2 δ 0 u ∧
        (∀ x y, L0 a b y (fun x' => u x' y) x = f x y) ∧ Centered μ u ∧
        ∃ C0 : ℝ, 0 < C0 ∧ ∃ m : ℝ, 0 < m ∧
          (∀ x y, |u x y| + ‖fderiv ℝ (fun x' => u x' y) x‖ +
              ‖iteratedFDeriv ℝ 2 (fun x' => u x' y) x‖ ≤ C0 * (1 + ‖x‖ ^ m)) ∧
          (∀ x1 x2 y, ‖iteratedFDeriv ℝ 2 (fun x' => u x' y) x1 -
              iteratedFDeriv ℝ 2 (fun x' => u x' y) x2‖ ≤
                C0 * min (‖x1 - x2‖ ^ δ) 1 * (1 + ‖x1‖ ^ m + ‖x2‖ ^ m))) ∧
      ∀ u v : E d1 → E d2 → ℝ, Cp2 δ 0 u → Cp2 δ 0 v →
        (∀ x y, L0 a b y (fun x' => u x' y) x = f x y) →
        (∀ x y, L0 a b y (fun x' => v x' y) x = f x y) →
        Centered μ u → Centered μ v → u = v := by sorry

end FullyCoupledSDE.Poisson
