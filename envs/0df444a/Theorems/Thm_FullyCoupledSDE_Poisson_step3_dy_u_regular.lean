-- Prove2me | Theorems.Thm_FullyCoupledSDE_Poisson_step3_dy_u_regular
-- name    : FullyCoupledSDE.Poisson.step3_dy_u_regular
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:25:41.065553+00:00
-- url     : https://prove2.me/theorems/45f935ea-b261-420d-a94b-2a56de79f205
-- title:
--   Proof of Theorem 2.1, Step 3, p. 1220 — for η = 1 the centered solution has ∂_y u ∈ C^{2+δ,0}_p and |∂_y u| ≤ C(1 + |x|^m)
-- statement:
--   Let $a,b$ satisfy (Aσ) and (Ab) and lie in $C^{\delta,1}_b$ with $0<\delta\le1$, let $(\mu^y)_y$ be the invariant family of $\mathscr L_0$, and let $f\in C^{\delta,1}_p$ be centered. If $u\in C^{2+\delta,0}_p$ is a centered solution of $\mathscr L_0(x,y)u(x,y)=f(x,y)$, then $u$ is continuously differentiable in $y$ with $\partial_yu\in C^{2+\delta,0}_p$, that is $u\in C^{2+\delta,1}_p$, and there are $C,m>0$ with
--   $$|\partial_yu(x,y)|\le C(1+|x|^m)\qquad\text{for all }x,y.$$
--
--   This yields (2.3) for $\eta=1$ and is the base of the induction over integer $\eta$.
--
--   **Formalization Note** Step 3 of the paper "only focus[es] on the a priori estimates": it differentiates the equation in $y$ assuming $\partial_yu$ exists. The statement here is the existence claim of Theorem 2.1 for $\eta=1$, applied to the (unique) centered solution of the $\eta=0$ case. $|\partial_yu|$ is the operator norm of the $y$-gradient.
-- source:
--   Röckner & Xie, Diffusion approximation for fully coupled SDEs, Ann. Probab. 49 (2021), p. 1220, proof of Theorem 2.1, Step 3 (case η = 1), bound on |∂_y u|

import Mathlib
import Definitions.Def_FullyCoupledSDE_Poisson_Setting

namespace FullyCoupledSDE.Poisson

open MeasureTheory

/-- Proof of Theorem 2.1, Step 3 (p. 1220), conclusion for `η = 1`. Under (Aσ), (Ab),
`a, b ∈ C^{δ,1}_b` and a centered `f ∈ C^{δ,1}_p`, every centered solution `u ∈ C^{2+δ,0}_p` of
(1.1) is `C¹` in `y` with `∂_y u ∈ C^{2+δ,0}_p` (i.e. `u ∈ C^{2+δ,1}_p`), and
`|∂_y u(x,y)| ≤ C(1 + |x|^m)`. -/
theorem step3_dy_u_regular {d1 d2 : ℕ} (hd1 : 1 ≤ d1) (hd2 : 1 ≤ d2)
    (a : E d1 → E d2 → Matrix (Fin d1) (Fin d1) ℝ) (b : E d1 → E d2 → E d1)
    (μ : E d2 → Measure (E d1)) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hσ : AssumpSigma a) (hb : AssumpB b) (ha : CbMat δ 1 a) (hbb : Cb δ 1 b)
    (hμ : IsInvariantFamily a b μ)
    (f : E d1 → E d2 → ℝ) (hf : Cp δ 1 f) (hfc : Centered μ f)
    (u : E d1 → E d2 → ℝ) (hu : Cp2 δ 0 u)
    (hsol : ∀ x y, L0 a b y (fun x' => u x' y) x = f x y) (huc : Centered μ u) :
    Cp2 δ 1 u ∧
      ∃ C : ℝ, 0 < C ∧ ∃ m : ℝ, 0 < m ∧
        ∀ x y, ‖fderiv ℝ (u x) y‖ ≤ C * (1 + ‖x‖ ^ m) := by sorry

end FullyCoupledSDE.Poisson
