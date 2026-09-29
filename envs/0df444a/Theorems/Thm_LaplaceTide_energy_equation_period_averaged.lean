-- Prove2me | Theorems.Thm_LaplaceTide_energy_equation_period_averaged
-- name    : LaplaceTide.energy_equation_period_averaged
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T21:35:00.320003+00:00
-- url     : https://prove2.me/theorems/9f9ed614-ce44-4106-98b1-987bb4ad0d0c
-- title:
--   Period-averaged energy balance $\nabla\cdot\langle P\rangle = \langle W_t\rangle + \langle u\cdot F\rangle$
-- statement:
--   **The period-averaged energy balance.**
--
--   Let the tide be periodic with period $T$. Averaging the energy equation
--   $KE_t + PE_t + \nabla\cdot\vec P = W_t + \vec u\cdot\vec F$ over one period annihilates the
--   two storage terms, by $\langle KE_t\rangle = \langle PE_t\rangle = 0$, and leaves
--
--   $$ \nabla\cdot\langle \vec P\rangle \;=\; \langle W_t\rangle + \langle \vec u\cdot\vec F\rangle, $$
--
--   equation (32) of the notes. This is the form of the energy budget used to infer tidal
--   dissipation from observations: integrated over a basin through whose boundary there is no
--   flow, the left-hand side integrates to zero and the work done by the tide generating potential
--   balances the dissipation.
--
--   The statement is made at a fixed horizontal position $(x,y)$, for a solution of Laplace's
--   tidal equations with the solid Earth tide included, under the hypotheses that the kinetic and
--   potential energy densities are $T$-periodic in time there with continuous time derivative.
--
--   **Formalization Note** The averaged divergence is formalized as the time average of
--   $\nabla\cdot\vec P$ at the fixed position $(x,y)$, that is, as
--   $\frac1T\int_0^T\big(\partial_x P^x + \partial_y P^y\big)\,\mathrm{d}t$; interchanging the
--   average with the horizontal derivatives is not part of the claim. Integrability of that
--   integrand over one period is assumed.
-- source:
--   M. Hendershott, Lecture 3: Solutions to Laplace's Tidal Equations, Woods Hole Oceanographic Institution GFD Program lecture notes, notes by V. Birman and E. Williams Frajka, pp. 34-44, https://www.whoi.edu/cms/files/lecture03_21374.pdf, p. 41, section 6, equation (32)

import Definitions.Def_LaplaceTide_core

namespace LaplaceTide

theorem energy_equation_period_averaged
    (f g rho : ℝ) (D : ℝ → ℝ → ℝ) (Gamma Fx Fy u v zeta delta : Field3)
    (x y T : ℝ) (hT : 0 < T)
    (hrho : 0 < rho) (hDpos : ∀ x y, 0 < D x y) (hD : PartialDiff₂ D)
    (hu : PartialDiff u) (hv : PartialDiff v) (hzeta : PartialDiff zeta)
    (hdelta : PartialDiff delta) (hGamma : PartialDiff Gamma)
    (hlte : IsLTE f g rho D Gamma Fx Fy u v zeta delta)
    (hKEper : Function.Periodic (fun s => kineticEnergy rho D u v x y s) T)
    (hPEper : Function.Periodic
      (fun s => potentialEnergy rho g D (observedTide zeta delta) delta x y s) T)
    (hKEcont : Continuous (fun s => dt (kineticEnergy rho D u v) x y s))
    (hPEcont : Continuous
      (fun s => dt (potentialEnergy rho g D (observedTide zeta delta) delta) x y s))
    (hflux : IntervalIntegrable
      (fun s => dx (energyFluxX rho g D u (observedTide zeta delta) delta) x y s
        + dy (energyFluxY rho g D v (observedTide zeta delta) delta) x y s)
      MeasureTheory.volume 0 T) :
    (1 / T) * ∫ t in (0 : ℝ)..T,
        (dx (energyFluxX rho g D u (observedTide zeta delta) delta) x y t
          + dy (energyFluxY rho g D v (observedTide zeta delta) delta) x y t)
      = (1 / T) * ∫ t in (0 : ℝ)..T,
        (workRate rho g D u v Gamma (observedTide zeta delta) delta x y t
          + (u x y t * Fx x y t + v x y t * Fy x y t)) := by sorry

end LaplaceTide
