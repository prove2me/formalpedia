-- Prove2me | Theorems.Thm_Larmor_poynting_flux_transverse
-- name    : Larmor.poynting_flux_transverse
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T01:20:17.155007+00:00
-- url     : https://prove2.me/theorems/33e3f57e-3cf7-4577-a8c5-19140f5337fc
-- title:
--   Poynting flux of a transverse pair: $\langle S,n\rangle=\varepsilon_0c(\|E\|^2-\langle E,n\rangle^2)$
-- statement:
--   **Normal Poynting flux of a transverse field pair.** Let $\varepsilon_0$ and $c$ be arbitrary, let $E\in\mathbb{R}^3$ be an electric field vector and let $n\in\mathbb{R}^3$ be a unit vector. If the magnetic field is $B=n\times E/c$, as it is for the Liénard–Wiechert fields with $n$ the unit vector from the retarded position of the charge to the observation point, then the flux density of electromagnetic energy through the surface with normal $n$ is
--
--   $$\langle S,n\rangle=\varepsilon_0c\bigl(\|E\|^2-\langle E,n\rangle^2\bigr),\qquad S=\varepsilon_0c^2\,(E\times B).$$
--
--   The right-hand side is $\varepsilon_0c\,\|E_\perp\|^2$, where $E_\perp$ is the component of $E$ orthogonal to $n$: only the transverse part of the electric field transports energy across the surface. In the Larmor configuration this is the step that removes the Coulomb term from the calculation, since for a charge instantaneously at rest that term is parallel to $n$.
--
--   **Formalization Note** The identity is stated for vectors, at a single point, and requires no positivity of $\varepsilon_0$ or $c$: for $c=0$ both sides vanish.
-- source:
--   https://en.wikipedia.org/wiki/Larmor_formula — Derivation section, where $\mathbf B=\mathbf n\times\mathbf E/c$ and the Poynting vector is integrated over the sphere; J. D. Jackson, Classical Electrodynamics, 3rd ed., Wiley 1998, §14.2.

import Definitions.Def_Larmor_em_fields

namespace Larmor

theorem poynting_flux_transverse (ε₀ c : ℝ) (Ev n : Vec) (hn : ‖n‖ = 1) :
    inner ℝ (poynting ε₀ c Ev (c⁻¹ • cross n Ev)) n
      = ε₀ * c * (‖Ev‖ ^ 2 - (inner ℝ Ev n : ℝ) ^ 2) := by sorry

end Larmor
