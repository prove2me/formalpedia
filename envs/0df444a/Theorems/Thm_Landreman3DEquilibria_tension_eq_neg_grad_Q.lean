-- Prove2me | Theorems.Thm_Landreman3DEquilibria_tension_eq_neg_grad_Q
-- name    : Landreman3DEquilibria.tension_eq_neg_grad_Q
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T18:59:42.072227+00:00
-- url     : https://prove2.me/theorems/df5c02ab-7f50-4b8e-8357-e3ff0290bcd1
-- title:
--   $(B\cdot\nabla)B=-\nabla Q$
-- statement:
--   Let $0<\epsilon<1$ and let $Q=\tfrac12\big(x_0^2+x_1^2+4x_2^2\big)$. At every point of $U_\epsilon$ the magnetic tension of the field of the integer-transform family is an exact gradient,
--
--   $$(B\cdot\nabla)B=-\nabla Q ,$$
--
--   equivalently $(B\cdot\nabla)B=-Dx$ with $D=\mathrm{diag}(1,1,4)$.
--
--   This identity is the analytic heart of the construction. Combined with the vector identity $(\nabla\times B)\times B=(B\cdot\nabla)B-\nabla\tfrac{|B|^2}{2}$ it yields exact scalar-pressure force balance, and it is also what makes each Cartesian coordinate along a field line a harmonic oscillator, with frequencies $1$, $1$ and $2$.
-- source:
--   M. Landreman, Analytic toroidal 3D MHD equilibria and steady Euler flows with invariant surfaces, J. Plasma Phys. (submitted), arXiv:2609.26742v1 (2026), https://arxiv.org/abs/2609.26742 , Section 2, eq. (2.8) and the text after eq. (2.9)

import Mathlib
import Definitions.Def_landreman_vector_calculus
import Definitions.Def_landreman_integer_iota_family

namespace Landreman3DEquilibria

theorem tension_eq_neg_grad_Q (e : ℝ) (he : 0 < e) (he1 : e < 1) (x : LVec)
    (hx : x ∈ domainU e) :
    tension (Bfield e) x = -grad Qfun x := by sorry

end Landreman3DEquilibria
