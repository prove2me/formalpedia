-- Prove2me | Theorems.Thm_FullyCoupledSDE_Poisson_theorem_2_1
-- name    : FullyCoupledSDE.Poisson.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:25:45.862627+00:00
-- url     : https://prove2.me/theorems/1c1b50f8-e367-4eb5-80e4-121cbbd424a8
-- title:
--   Theorem 2.1, p. 1210 — the centered Poisson equation L0(x,y)u = f has a unique centered solution in C^{2+δ,η}_p, with (2.1)–(2.3)
-- statement:
--   Let $d_1,d_2\ge1$. Let the coefficients $a(x,y)$ (a $d_1\times d_1$ matrix) and $b(x,y)\in\mathbb R^{d_1}$ satisfy the nondegeneracy condition (Aσ) and the recurrence condition (Ab), and assume $a,b\in C^{\delta,\eta}_b$ with $0<\delta\le1$ and $\eta\ge0$. Let $(\mu^y)_{y\in\mathbb R^{d_2}}$ be the invariant family of the frozen operator
--   $$\mathscr L_0(x,y)=\sum_{i,j=1}^{d_1}a^{ij}(x,y)\frac{\partial^2}{\partial x_i\partial x_j}+\sum_{i=1}^{d_1}b^i(x,y)\frac{\partial}{\partial x_i}.$$
--   Then for every $f\in C^{\delta,\eta}_p$ satisfying the centering condition $\int f(x,y)\,\mu^y(dx)=0$ for all $y$ (1.3):
--
--   1. there is $u\in C^{2+\delta,\eta}_p$ solving $\mathscr L_0(x,y)u(x,y)=f(x,y)$ for all $x,y$ (1.1) and satisfying (1.3), together with constants $C_0,m>0$ such that, for all $x,x_1,x_2\in\mathbb R^{d_1}$ and $y\in\mathbb R^{d_2}$,
--   $$|u(x,y)|+|\nabla_xu(x,y)|+|\nabla^2_xu(x,y)|\le C_0(1+|x|^m),\qquad(2.1)$$
--   $$|\nabla^2_xu(x_1,y)-\nabla^2_xu(x_2,y)|\le C_0(|x_1-x_2|^\delta\wedge1)(1+|x_1|^m+|x_2|^m),\qquad(2.2)$$
--   and, if $\eta>0$, for every $x$,
--   $$\|u(x,\cdot)\|_{C^\eta_b}\le C_0(1+|x|^m);\qquad(2.3)$$
--   2. this solution is unique: two solutions of (1.1) in $C^{2+\delta,\eta}_p$ that both satisfy (1.3) are equal.
--
--   The theorem gives optimal regularity of the Poisson solution in $x$ (two derivatives plus the Hölder exponent of the data) and the same regularity in the parameter $y$ as the coefficients and $f$. It is the tool behind the diffusion approximation of fully coupled multiscale SDEs in §§4–5 of the paper.
--
--   **Formalization Note** $\mu^y$ is the infinitesimally invariant probability measure of $\mathscr L_0(\cdot,y)$ (equivalently, the invariant measure of the frozen SDE (1.7)). The constants $C_0,m$ exist for each fixed $(a,b,f)$; the paper's dependence clause ("depending only on $d_1,d_2$, $\|a\|_{C^{\delta,0}_b}$, $\|b\|_{C^{\delta,0}_b}$, $[f]_{C^{\delta,0}_p}$") and the recursive constant $\mathcal K_\eta$ of (2.4)–(2.5), absorbed into $C_0$ in (2.3), are not posed, since the dependence clause is false as printed. (2.1)–(2.2), labelled "Case η = 0", are asserted for every $\eta\ge0$; they follow from the $\eta=0$ case because $C^{\delta,\eta}\subset C^{\delta,0}$ and the solution is unique. Uniqueness is stated for the whole class $C^{2+\delta,\eta}_p$. Norms of $\nabla_xu$, $\nabla^2_xu$ are operator norms; the $C^\eta_b$ norm is in max form.
-- source:
--   Röckner & Xie, Diffusion approximation for fully coupled SDEs, Ann. Probab. 49 (2021), p. 1210, Theorem 2.1, (2.1)–(2.3); proof pp. 1217–1222

import Mathlib
import Definitions.Def_FullyCoupledSDE_Poisson_Setting

namespace FullyCoupledSDE.Poisson

open MeasureTheory

/-- Theorem 2.1 (p. 1210). Under (Aσ), (Ab) and `a, b ∈ C^{δ,η}_b` (`0 < δ ≤ 1`, `η ≥ 0`), for every
centered `f ∈ C^{δ,η}_p` the Poisson equation (1.1) `L0(x,y)u(x,y) = f(x,y)` has a centered solution
`u ∈ C^{2+δ,η}_p` satisfying (2.1), (2.2) and, for `η > 0`, (2.3); and any two centered solutions
in `C^{2+δ,η}_p` coincide. -/
theorem theorem_2_1 {d1 d2 : ℕ} (hd1 : 1 ≤ d1) (hd2 : 1 ≤ d2)
    (a : E d1 → E d2 → Matrix (Fin d1) (Fin d1) ℝ) (b : E d1 → E d2 → E d1)
    (μ : E d2 → Measure (E d1)) (δ η : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : 0 ≤ η)
    (hσ : AssumpSigma a) (hb : AssumpB b) (ha : CbMat δ η a) (hbb : Cb δ η b)
    (hμ : IsInvariantFamily a b μ)
    (f : E d1 → E d2 → ℝ) (hf : Cp δ η f) (hfc : Centered μ f) :
    (∃ u : E d1 → E d2 → ℝ, Cp2 δ η u ∧
        (∀ x y, L0 a b y (fun x' => u x' y) x = f x y) ∧ Centered μ u ∧
        ∃ C0 : ℝ, 0 < C0 ∧ ∃ m : ℝ, 0 < m ∧
          (∀ x y, |u x y| + ‖fderiv ℝ (fun x' => u x' y) x‖ +
              ‖iteratedFDeriv ℝ 2 (fun x' => u x' y) x‖ ≤ C0 * (1 + ‖x‖ ^ m)) ∧
          (∀ x1 x2 y, ‖iteratedFDeriv ℝ 2 (fun x' => u x' y) x1 -
              iteratedFDeriv ℝ 2 (fun x' => u x' y) x2‖ ≤
                C0 * min (‖x1 - x2‖ ^ δ) 1 * (1 + ‖x1‖ ^ m + ‖x2‖ ^ m)) ∧
          (0 < η → ∀ x, CbYNormLe η (u x) (C0 * (1 + ‖x‖ ^ m)))) ∧
      ∀ u v : E d1 → E d2 → ℝ, Cp2 δ η u → Cp2 δ η v →
        (∀ x y, L0 a b y (fun x' => u x' y) x = f x y) →
        (∀ x y, L0 a b y (fun x' => v x' y) x = f x y) →
        Centered μ u → Centered μ v → u = v := by sorry

end FullyCoupledSDE.Poisson
