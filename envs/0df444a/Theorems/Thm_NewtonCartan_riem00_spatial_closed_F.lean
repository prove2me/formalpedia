-- Prove2me | Theorems.Thm_NewtonCartan_riem00_spatial_closed_F
-- name    : NewtonCartan.riem00_spatial_closed_F
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T06:37:33.049694+00:00
-- url     : https://prove2.me/theorems/06c8f658-5368-4310-a348-878a728d2a4d
-- title:
--   Trautman $F^a{}_d=R^a{}_{00d}$ is spatially closed as a Hessian
-- statement:
--   Assume a classical connection $\widetilde{\nabla}$ on $(\mathbb{R}^4,t_a,h^{ab})$ satisfies CurvConds for smooth $\rho$ and that its Riemann tensor has the Trautman form
--   $$
--   R^a{}_{bcd}=t_b(t_c F^a{}_d-t_d F^a{}_c),\qquad F^a{}_d=R^a{}_{00d}.
--   $$
--   Then $F$ is smooth and satisfies $F^0{}_d=0$, $F^a{}_0=0$, $F^i{}_j=F^j{}_i$, the *spatial* closed-Hessian identity
--   $$
--   \partial_k F^i{}_j=\partial_j F^i{}_k\qquad(i,j,k\in\{1,2,3\}),
--   $$
--   and $\sum_i F^i{}_i=4\pi\rho$.
--
--   Temporal closedness need not hold: $\Gamma^i{}_{00}=x^i f(t)$ yields $F^i{}_j=\delta^i{}_j f(t)$ with $\partial_0 F\neq 0$. Spatial closedness is the integrability needed to recover $\varphi$ slicewise.
--
--   Formalization Note. Corrects the retired `riem00_is_closed_F`. Uses `classical_christoffel_form`.
-- source:
--   Malament Prop. 4.2.5 / Weatherall Prop. 2.2

import Definitions.Def_NewtonCartan_defs

open scoped ContDiff

namespace NewtonCartan

/-- Under CurvConds and the Trautman $t_b$-form, $F^a{}_d := R^a{}_{00d}$ is smooth, vanishes on
temporal indices, is symmetric, and is closed as a Hessian in the *spatial* indices; its trace is $4\pi\rho$.
(Temporal closedness $\partial_0 F^i{}_j = \partial_j F^i{}_0$ can fail, e.g. $\Gamma^i{}_{00}=x^i f(t)$.) -/
theorem riem00_spatial_closed_F (Γt : Conn) (ρ : E → ℝ)
    (hΓt : IsClassical Γt) (hρ : ContDiff ℝ ∞ ρ) (hcurv : CurvConds Γt ρ)
    (hform : ∀ x a b c d,
      riem Γt x a b c d =
        tt b * (tt c * riem Γt x a 0 0 d - tt d * riem Γt x a 0 0 c)) :
    let F : E → Fin 4 → Fin 4 → ℝ := fun x a d => riem Γt x a 0 0 d
    ContDiff ℝ ∞ F ∧
      (∀ x d, F x 0 d = 0) ∧ (∀ x a, F x a 0 = 0) ∧
      (∀ x i j, F x i j = F x j i) ∧
      (∀ x i j k, i ≠ 0 → j ≠ 0 → k ≠ 0 →
        pd (fun y => F y i j) k x = pd (fun y => F y i k) j x) ∧
      (∀ x, ∑ i : Fin 4, F x i i = 4 * Real.pi * ρ x) := by sorry

end NewtonCartan
