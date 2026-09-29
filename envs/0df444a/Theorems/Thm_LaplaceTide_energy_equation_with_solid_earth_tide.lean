-- Prove2me | Theorems.Thm_LaplaceTide_energy_equation_with_solid_earth_tide
-- name    : LaplaceTide.energy_equation_with_solid_earth_tide
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T21:36:46.497043+00:00
-- url     : https://prove2.me/theorems/2a2062e6-416d-4aee-98d6-eefa99c17277
-- title:
--   Energy equation of the tides including the solid Earth tide
-- statement:
--   **The energy equation of the tides, including the solid Earth tide.**
--
--   The crust yields elastically to the tidal load, so the sea floor moves with the solid Earth
--   tide $\delta$ and the observed, geocentric tide is $\zeta_0 = \zeta - \delta$. The continuity
--   equation becomes $(\zeta-\delta)_t + \nabla\cdot\vec u D = 0$, and repeating the energy
--   derivation gives the pointwise balance
--
--   $$ KE_t + PE_t + \nabla\cdot \vec P \;=\; W_t + \vec u\cdot\vec F $$
--
--   with
--
--   $$ KE = \tfrac12\rho D(u^2+v^2), \qquad PE = \tfrac12\rho g\big(\zeta_0^2 + 2\zeta_0\delta + 2\delta D\big), $$
--
--   $$ \vec P = \rho g D \vec u (\zeta_0+\delta), \qquad
--      W_t = \rho \zeta_{0t}\Gamma + \rho \nabla\cdot(\vec u D\Gamma) + \rho g(\zeta_0+D)\delta_t . $$
--
--   These are equations (35)–(39) of the notes. The result holds pointwise for any solution of
--   Laplace's tidal equations, for a variable bottom topography $D(x,y)$, with no assumption on
--   the form of the dissipative force and no averaging; taking $\delta \equiv 0$ recovers the
--   energy equation with the solid Earth tide ignored.
--
--   Together with the vanishing of the period-averaged storage terms, this identity is the
--   starting point of the estimates of global tidal dissipation from altimetry, where
--   $\int\langle \vec u\cdot\vec F\rangle$ is obtained as a residual from the observed tide.
--
--   **Formalization Note** The depth $D$ is a function of $x$ and $y$ only, and the density
--   $\rho>0$ and depth $D>0$ are positive because the momentum equations carry $F^x/(\rho D)$.
--   All fields are assumed differentiable in each variable separately. The potential energy is the
--   expression printed in equation (37), which differs from
--   $\int_{-D+\delta}^{\zeta}\rho g z\,\mathrm{d}z$ by a term independent of time and therefore
--   has the same time derivative.
-- source:
--   M. Hendershott, Lecture 3: Solutions to Laplace's Tidal Equations, Woods Hole Oceanographic Institution GFD Program lecture notes, notes by V. Birman and E. Williams Frajka, pp. 34-44, https://www.whoi.edu/cms/files/lecture03_21374.pdf, pp. 42, section 6.1, equations (35), (36), (37), (38), (39)

import Definitions.Def_LaplaceTide_core

namespace LaplaceTide

theorem energy_equation_with_solid_earth_tide
    (f g rho : ℝ) (D : ℝ → ℝ → ℝ) (Gamma Fx Fy u v zeta delta : Field3)
    (hrho : 0 < rho) (hDpos : ∀ x y, 0 < D x y) (hD : PartialDiff₂ D)
    (hu : PartialDiff u) (hv : PartialDiff v) (hzeta : PartialDiff zeta)
    (hdelta : PartialDiff delta) (hGamma : PartialDiff Gamma)
    (hlte : IsLTE f g rho D Gamma Fx Fy u v zeta delta) :
    ∀ x y t, dt (kineticEnergy rho D u v) x y t
      + dt (potentialEnergy rho g D (observedTide zeta delta) delta) x y t
      + dx (energyFluxX rho g D u (observedTide zeta delta) delta) x y t
      + dy (energyFluxY rho g D v (observedTide zeta delta) delta) x y t
      = workRate rho g D u v Gamma (observedTide zeta delta) delta x y t
        + (u x y t * Fx x y t + v x y t * Fy x y t) := by sorry

end LaplaceTide
