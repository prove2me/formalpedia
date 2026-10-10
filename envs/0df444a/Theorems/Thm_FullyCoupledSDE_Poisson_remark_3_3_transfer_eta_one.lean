-- Prove2me | Theorems.Thm_FullyCoupledSDE_Poisson_remark_3_3_transfer_eta_one
-- name    : FullyCoupledSDE.Poisson.remark_3_3_transfer_eta_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:25:36.731637+00:00
-- url     : https://prove2.me/theorems/3071044d-63ae-451a-b7b8-cc44487e57b5
-- title:
--   Remark 3.3(ii), p. 1215 — for η = 1: ∂_y ∫h μ^y(dx) = ∫[∂_y h − ∂_yL0 · u] μ^y(dx) when u ∈ C^{2+δ,0}_p solves (1.1)
-- statement:
--   Let $a,b$ satisfy (Aσ) and (Ab) and lie in $C^{\delta,1}_b$ with $0<\delta\le1$, and let $(\mu^y)_y$ be the invariant family of $\mathscr L_0$. Let $h\in C^{\delta,1}_p$, write $\bar h(y)=\int h(x,y)\,\mu^y(dx)$, and let $u\in C^{2+\delta,0}_p$ solve the Poisson equation
--   $$\mathscr L_0(x,y)u(x,y)=h(x,y)-\bar h(y)\qquad\text{for all }x,y.$$
--   Then $\bar h$ is differentiable, and for every $y$ and every direction $v\in\mathbb R^{d_2}$ the function $x\mapsto\partial_yh(x,y)\cdot v-\big(\tfrac{\partial\mathscr L_0}{\partial y}(x,y)\cdot v\big)u(x,y)$ is $\mu^y$-integrable with
--   $$\partial_y\bar h(y)\cdot v=\int_{\mathbb R^{d_1}}\Big[\partial_yh(x,y)\cdot v-\Big(\frac{\partial\mathscr L_0}{\partial y}(x,y)\cdot v\Big)u(x,y)\Big]\,\mu^y(dx).$$
--
--   This is the case $\eta=1$ of Lemma 3.2(i), formula (3.9). It is a transfer formula: the $y$-derivative of an average against $\mu^y$ is expressed through $x$-derivatives of the Poisson solution $u$, with no derivative of $\mu^y$ in $y$.
--
--   **Formalization Note** $\partial_y$ is taken in a direction $v$ (`fderiv … y v`); the full gradient is determined by its directional values. Integrability of the integrand is part of the conclusion, so the formula cannot hold through a junk zero integral. The solution $u$ is any solution in $C^{2+\delta,0}_p$; it need not be centered.
-- source:
--   Röckner & Xie, Diffusion approximation for fully coupled SDEs, Ann. Probab. 49 (2021), p. 1215, Remark 3.3(ii) (display); Lemma 3.2(i), (3.9) with η = 1, p. 1214

import Mathlib
import Definitions.Def_FullyCoupledSDE_Poisson_Setting

namespace FullyCoupledSDE.Poisson

open MeasureTheory

/-- Remark 3.3(ii) (p. 1215), i.e. Lemma 3.2(i) (3.9) for `η = 1`. Under (Aσ), (Ab),
`a, b ∈ C^{δ,1}_b`, let `h ∈ C^{δ,1}_p` and let `u ∈ C^{2+δ,0}_p` solve
`L0(x,y)u(x,y) = h(x,y) − h̄(y)`. Then `h̄` is differentiable and, for every direction `v`,
`∂_y h̄(y)·v = ∫ [∂_y h(x,y)·v − (∂L0/∂y)(x,y)·v u(x,y)] μ^y(dx)`, the integrand being integrable. -/
theorem remark_3_3_transfer_eta_one {d1 d2 : ℕ} (hd1 : 1 ≤ d1) (hd2 : 1 ≤ d2)
    (a : E d1 → E d2 → Matrix (Fin d1) (Fin d1) ℝ) (b : E d1 → E d2 → E d1)
    (μ : E d2 → Measure (E d1)) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hσ : AssumpSigma a) (hb : AssumpB b) (ha : CbMat δ 1 a) (hbb : Cb δ 1 b)
    (hμ : IsInvariantFamily a b μ)
    (h : E d1 → E d2 → ℝ) (hh : Cp δ 1 h)
    (u : E d1 → E d2 → ℝ) (hu : Cp2 δ 0 u)
    (hsol : ∀ x y, L0 a b y (fun x' => u x' y) x = h x y - avg μ h y) :
    ∀ y : E d2, DifferentiableAt ℝ (avg μ h) y ∧
      ∀ v : E d2,
        Integrable (fun x => fderiv ℝ (h x) y v - dL0 a b y v (fun x' => u x' y) x) (μ y) ∧
        fderiv ℝ (avg μ h) y v =
          ∫ x, (fderiv ℝ (h x) y v - dL0 a b y v (fun x' => u x' y) x) ∂(μ y) := by sorry

end FullyCoupledSDE.Poisson
