-- Prove2me | Theorems.Thm_NewtonCartan_gauge_NG_poisson_of_spatial_hess
-- name    : NewtonCartan.gauge_NG_poisson_of_spatial_hess
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T06:37:33.140272+00:00
-- url     : https://prove2.me/theorems/cb44a392-09c6-4173-89cf-ec9b0d88c974
-- title:
--   Gauge by a spatial Hessian potential of $R^a{}_{00d}$ is NG and obeys Poisson
-- statement:
--   Let $\widetilde{\nabla}$ be classical, satisfy CurvConds for $\rho$, and have Trautman-form Riemann. Let $\varphi$ be smooth with
--   $$
--   \partial_j(\nabla^i\varphi)=R^i{}_{00j}\qquad(i,j\text{ spatial}).
--   $$
--   Then $\nabla=(\widetilde{\nabla},t_b t_c\nabla^a\varphi)$ is flat and compatible, and $\nabla^a\nabla_a\varphi=4\pi\rho$.
--
--   Only spatial Hessian matching is required: the gauge modifies solely $\Gamma^a{}_{00}$, and flatness of the resulting $R^i{}_{00j}$ is exactly $\partial_j(g^i-\partial^i\varphi)=0$ after accounting for Coriolis/centrifugal terms already present in $R^i{}_{00j}$.
--
--   Formalization Note. Corrects the retired `gauge_NG_poisson_of_hessF`.
-- source:
--   Malament Prop. 4.2.5 / Weatherall Prop. 2.2

import Definitions.Def_NewtonCartan_defs

open scoped ContDiff

namespace NewtonCartan

/-- If $\partial_j(\nabla^i\varphi)=R^i{}_{00j}$ for spatial indices and $\Gamma t$ is classical with Trautman
form and CurvConds, then `gaugeΓ Γt φ` is NG and satisfies Poisson. -/
theorem gauge_NG_poisson_of_spatial_hess (Γt : Conn) (ρ : E → ℝ) (φ : E → ℝ)
    (hΓt : IsClassical Γt) (hρ : ContDiff ℝ ∞ ρ) (hcurv : CurvConds Γt ρ)
    (hφ : ContDiff ℝ ∞ φ)
    (hform : ∀ x a b c d,
      riem Γt x a b c d =
        tt b * (tt c * riem Γt x a 0 0 d - tt d * riem Γt x a 0 0 c))
    (hhess : ∀ x i j, i ≠ 0 → j ≠ 0 →
      pd (fun y => gradUp φ y i) j x = riem Γt x i 0 0 j) :
    IsNG (gaugeΓ Γt φ) φ ∧ Poisson (gaugeΓ Γt φ) φ ρ := by sorry

end NewtonCartan
