-- Prove2me | Theorems.Thm_Landreman3DEquilibria_force_balance
-- name    : Landreman3DEquilibria.force_balance
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T19:00:29.698104+00:00
-- url     : https://prove2.me/theorems/7601b674-22d1-4c1d-a286-436e49e9e44a
-- title:
--   Exact force balance $(\nabla\times B)\times B=\nabla p$
-- statement:
--   Let $0<\epsilon<1$, let $p_a$ be an arbitrary constant, and let
--
--   $$\psi=\frac{x_0^2+x_1^2+4x_2^2+|B|^2-2+\epsilon^2}{4},\qquad p=p_a-2\psi .$$
--
--   Then at every point of $U_\epsilon$ the field and the pressure satisfy the MHD force-balance equation
--
--   $$(\nabla\times B)\times B=\nabla p .$$
--
--   Together with $\nabla\cdot B=0$ this says that $(B,p)$ is an exact solution of the ideal MHD equilibrium equations, equivalently that $B$ is a steady incompressible Euler velocity with hydrodynamic pressure $Q$ and Bernoulli function $H=Q+|B|^2/2$. The pressure is non-constant, which is what makes the solution relevant to Grad's conjecture.
-- source:
--   M. Landreman, Analytic toroidal 3D MHD equilibria and steady Euler flows with invariant surfaces, J. Plasma Phys. (submitted), arXiv:2609.26742v1 (2026), https://arxiv.org/abs/2609.26742 , Section 2, eqs. (2.4) and (2.5)

import Mathlib
import Definitions.Def_landreman_vector_calculus
import Definitions.Def_landreman_integer_iota_family

namespace Landreman3DEquilibria

theorem force_balance (e pa : ℝ) (he : 0 < e) (he1 : e < 1) (x : LVec) (hx : x ∈ domainU e) :
    cross3 (curl (Bfield e) x) (Bfield e x) = grad (pressure e pa) x := by sorry

end Landreman3DEquilibria
