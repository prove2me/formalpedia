-- Prove2me | Theorems.Thm_NoHair_spherical_electrovac_radial_equations
-- name    : NoHair.spherical_electrovac_radial_equations
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-22T20:52:31.577231+00:00
-- url     : https://prove2.me/theorems/1cb23438-bbd3-4b44-b729-6bbc0df906fd
-- title:
--   Radial Einstein–Maxwell equations for the two fluxes and the spherical mass
-- statement:
--   Let $g$ be a smooth Lorentzian metric and $F$ a smooth electromagnetic two-form satisfying the source-free Einstein–Maxwell equations. Suppose an open region has a spherical areal chart on $r>R$, with $R>0$. Let $A$ be its squared lapse and let $q,p$ be the radial coefficients of the unit Coulomb field and its Hodge dual in the chart.
--
--   At each exterior radius the two Maxwell equations and the radial Einstein equation give
--
--   $$
--   q'(r)=0,\qquad p'(r)=0,\qquad
--   \frac{d}{dr}\bigl[r(1-A(r))\bigr]=\frac{q(r)^2+p(r)^2}{r^2}.
--   $$
--
--   The two flux coefficients are normalized using the same unit field. With this convention electric and magnetic fluxes contribute equally to the derivative of twice the spherical mass.
-- source:
--   H. S. Reall, Part III Black Holes (2024), §6.1, p. 82, equations (6.2)–(6.6), https://www.damtp.cam.ac.uk/user/hsr1000/black_holes_lectures_2024.pdf. Differential form in the mission’s areal Kerr–Schild coordinates.

import Definitions.Def_NoHair_sphericalArealExterior

open scoped ContDiff Manifold

theorem NoHair.spherical_electrovac_radial_equations {M : Type*}
    [TopologicalSpace M] [ChartedSpace NoHair.E4 M] [IsManifold 𝓘(ℝ, NoHair.E4) ∞ M]
    (g F : NoHair.BilinField M) {D : Set M} (S : NoHair.SphericalArealExterior g F D)
    (hg : NoHair.IsLorentzian g) (hgs : NoHair.IsSmoothBilinField g)
    (hFs : NoHair.IsSmoothBilinField F) (hF : NoHair.IsTwoForm F) (he : NoHair.IsElectrovac g F) :
    ∀ r, S.horizonRadius < r →
      HasDerivAt S.electricFlux 0 r ∧ HasDerivAt S.magneticFlux 0 r ∧
      HasDerivAt (fun s => s * (1 - S.lapseSq s))
        ((S.electricFlux r ^ 2 + S.magneticFlux r ^ 2) / r ^ 2) r := by
  sorry
