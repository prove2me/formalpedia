-- Prove2me | Theorems.Thm_LaplaceTide_energy_equation_no_solid_earth_tide
-- name    : LaplaceTide.energy_equation_no_solid_earth_tide
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T21:34:16.929598+00:00
-- url     : https://prove2.me/theorems/55dce397-fb50-437f-b415-1b98eb7c1d36
-- title:
--   Energy equation of the tides, solid Earth tide ignored
-- statement:
--   **The energy equation of the tides, ignoring the solid Earth tide.**
--
--   Take Laplace's tidal equations over an ocean of constant depth $D$, with constant density
--   $\rho$ and gravity $g$, with tide generating potential $\Gamma$ and dissipative force
--   $(F^x,F^y)$, and with the solid Earth tide ignored, so that the continuity equation is
--   $\zeta_t + (uD)_x + (vD)_y = 0$. Multiplying the two momentum equations by $\rho u D$ and
--   $\rho v D$, the continuity equation by $\rho g \zeta$, and adding gives the pointwise energy
--   balance
--
--   $$ \tfrac12 \rho D\,(u^2+v^2)_t \;+\; \tfrac12 \rho g\,(\zeta^2)_t \;+\;
--      \nabla\cdot\big(\rho g \zeta \vec u D\big)
--      \;=\; \rho\,\zeta_t \Gamma + \nabla\cdot\big(\rho \vec u D \Gamma\big)
--      + \vec u \cdot \vec F, $$
--
--   which is equation (29) of the notes: the rate of change of kinetic and potential energy plus
--   the divergence of the energy flux equals the work done by fluid crossing equipotentials,
--   vertically and horizontally, plus the work of the dissipative forces — equation (30).
--
--   **Formalization Note** The notes print the second term of (29) as $\frac1g \rho g (\zeta^2)_t$;
--   the coefficient for which the identity is an exact consequence of the equations is
--   $\frac12 \rho g$, and that is what is stated here. The divergences are written out as the sum
--   of the two partial derivatives of the corresponding scalar components. The velocity,
--   elevation and potential fields are assumed differentiable in each variable separately, and
--   $\rho > 0$, $D > 0$ are needed because the momentum equations carry $F^x/(\rho D)$.
-- source:
--   M. Hendershott, Lecture 3: Solutions to Laplace's Tidal Equations, Woods Hole Oceanographic Institution GFD Program lecture notes, notes by V. Birman and E. Williams Frajka, pp. 34-44, https://www.whoi.edu/cms/files/lecture03_21374.pdf, p. 41, section 6, equations (29) and (30)

import Definitions.Def_LaplaceTide_core

namespace LaplaceTide

theorem energy_equation_no_solid_earth_tide
    (f g rho Dc : ℝ) (Gamma Fx Fy u v zeta : Field3)
    (hrho : 0 < rho) (hDc : 0 < Dc)
    (hu : PartialDiff u) (hv : PartialDiff v) (hzeta : PartialDiff zeta)
    (hGamma : PartialDiff Gamma)
    (hlte : IsLTE f g rho (fun _ _ => Dc) Gamma Fx Fy u v zeta (fun _ _ _ => 0)) :
    ∀ x y t,
      1 / 2 * rho * Dc * dt (fun x y t => (u x y t) ^ 2 + (v x y t) ^ 2) x y t
        + 1 / 2 * rho * g * dt (fun x y t => (zeta x y t) ^ 2) x y t
        + (dx (fun x y t => rho * g * zeta x y t * u x y t * Dc) x y t
          + dy (fun x y t => rho * g * zeta x y t * v x y t * Dc) x y t)
      = rho * dt zeta x y t * Gamma x y t
        + (dx (fun x y t => rho * u x y t * Dc * Gamma x y t) x y t
          + dy (fun x y t => rho * v x y t * Dc * Gamma x y t) x y t)
        + (u x y t * Fx x y t + v x y t * Fy x y t) := by sorry

end LaplaceTide
