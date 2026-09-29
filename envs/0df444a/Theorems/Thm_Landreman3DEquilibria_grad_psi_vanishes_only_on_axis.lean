-- Prove2me | Theorems.Thm_Landreman3DEquilibria_grad_psi_vanishes_only_on_axis
-- name    : Landreman3DEquilibria.grad_psi_vanishes_only_on_axis
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T19:20:05.340336+00:00
-- url     : https://prove2.me/theorems/18d7fdd7-c59b-4e22-83ec-d8a66e556b17
-- title:
--   $\nabla\psi=0$ exactly on the magnetic axis
-- statement:
--   Let $0<\epsilon<1$ and $0<\delta<(1-\epsilon)^2/4$, and let
--
--   $$\Omega_\delta=\{x\in U_\epsilon:\psi(x)\le\delta\}$$
--
--   be the solid toroidal plasma domain. For every $x\in\Omega_\delta$,
--
--   $$\nabla\psi(x)=0\iff\psi(x)=0 ,$$
--
--   that is, the gradient of the flux label — and hence, since $p=p_a-2\psi$, the pressure gradient — vanishes exactly on the magnetic axis $\{\psi=0\}$ and nowhere else in the plasma domain.
--
--   This is the precise sense in which the equilibrium has a genuinely non-constant pressure: the pressure gradient is non-zero on every flux surface except the degenerate one.
-- source:
--   M. Landreman, Analytic toroidal 3D MHD equilibria and steady Euler flows with invariant surfaces, J. Plasma Phys. (submitted), arXiv:2609.26742v1 (2026), https://arxiv.org/abs/2609.26742 , Section 2, Section 2.3, text after eq. (2.15) ('The gradient ∇ψ vanishes only on the field line u = -ε/2, v = 0'), with eqs. (2.17)-(2.18)

import Mathlib
import Definitions.Def_landreman_vector_calculus
import Definitions.Def_landreman_integer_iota_family

namespace Landreman3DEquilibria

theorem grad_psi_vanishes_only_on_axis (e d : ℝ) (he : 0 < e) (he1 : e < 1) (hd : 0 < d)
    (hd' : d < (1 - e) ^ 2 / 4) (x : LVec) (hx : x ∈ domainOmega e d) :
    grad (psiFun e) x = 0 ↔ psiFun e x = 0 := by sorry

end Landreman3DEquilibria
