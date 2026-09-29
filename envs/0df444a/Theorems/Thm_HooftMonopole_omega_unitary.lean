-- Prove2me | Theorems.Thm_HooftMonopole_omega_unitary
-- name    : HooftMonopole.omega_unitary
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T19:54:26.550947+00:00
-- url     : https://prove2.me/theorems/ffe678af-e99a-40b6-8400-d9b4f23e232f
-- title:
--   Eq. (1.5): the gauge transformation $\Omega(\theta,\varphi)$ is unitary
-- statement:
--   Let $\theta,\varphi$ be real numbers and let $\Omega(\theta,\varphi)$ be the $2\times2$ complex matrix of eq. (1.4),
--   $$\Omega(\theta,\varphi) = \cos\tfrac{\theta}{2}\begin{pmatrix}e^{i\varphi}&0\\0&e^{-i\varphi}\end{pmatrix} + \sin\tfrac{\theta}{2}\begin{pmatrix}0&i\\i&0\end{pmatrix}.$$
--   Then $\Omega$ is unitary:
--   $$\Omega(\theta,\varphi)\,\Omega(\theta,\varphi)^\dagger = 1 .$$
--
--   This shows that (1.4) is a genuine gauge transformation; it is the rotation used to build the hedgehog boundary condition of the Higgs field.
-- source:
--   G. 't Hooft, Magnetic monopoles in unified gauge theories, Nucl. Phys. B79 (1974) 276-284, https://doi.org/10.1016/0550-3213(74)90486-6, p. 278, eqs. (1.4)-(1.5)

import Mathlib
import Definitions.Def_HooftMonopole_Defs

open MeasureTheory Filter Topology Real

namespace HooftMonopole

theorem omega_unitary (θ φ : ℝ) :
    omegaMatrix θ φ * (omegaMatrix θ φ).conjTranspose = 1 := by sorry

end HooftMonopole
