-- Prove2me | Theorems.Thm_HooftMonopole_omega_adjoint_action
-- name    : HooftMonopole.omega_adjoint_action
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T19:55:42.474254+00:00
-- url     : https://prove2.me/theorems/2723d5f4-fa29-484b-b75a-f5134995a4f1
-- title:
--   Eq. (2.6): $\Omega$ rotates the isovector $(0,0,1)$ to a radial unit isovector
-- statement:
--   Let $\sigma_1,\sigma_2,\sigma_3$ be the Pauli matrices and $\Omega(\theta,\varphi)$ the SU(2) matrix (1.4). An isovector $v\in\mathbb R^3$ corresponds to the matrix $v\cdot\vec\sigma$, and $\Omega$ acts by conjugation. For all real $\theta,\varphi$,
--   $$\Omega(\theta,\varphi)\,\sigma_3\,\Omega(\theta,\varphi)^\dagger = \sin\theta\sin\varphi\;\sigma_1 + \sin\theta\cos\varphi\;\sigma_2 + \cos\theta\;\sigma_3 .$$
--   So $\Omega$ maps the isovector $(0,0,1)$ to the unit vector $(\sin\theta\sin\varphi,\ \sin\theta\cos\varphi,\ \cos\theta)$.
--
--   This is the computation behind eq. (2.6): the gauge-rotated Higgs vacuum points radially, which gives the monopole boundary condition.
--
--   **Formalization Note** The printed eq. (2.6) reads $(\sin\theta\cos\varphi, \sin\theta\sin\varphi, \cos\theta)$; with the standard Pauli matrices and the matrix (1.4) as printed, the first two components come out interchanged. The statement records the identity that actually holds.
-- source:
--   G. 't Hooft, Magnetic monopoles in unified gauge theories, Nucl. Phys. B79 (1974) 276-284, https://doi.org/10.1016/0550-3213(74)90486-6, p. 279, eq. (2.6) (with eq. (1.4))

import Mathlib
import Definitions.Def_HooftMonopole_Defs

open MeasureTheory Filter Topology Real

namespace HooftMonopole

theorem omega_adjoint_action (θ φ : ℝ) :
    omegaMatrix θ φ * pauli 2 * (omegaMatrix θ φ).conjTranspose =
      ((Real.sin θ * Real.sin φ : ℝ) : ℂ) • pauli 0
        + ((Real.sin θ * Real.cos φ : ℝ) : ℂ) • pauli 1
        + ((Real.cos θ : ℝ) : ℂ) • pauli 2 := by sorry

end HooftMonopole
