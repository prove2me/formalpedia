-- Prove2me | Theorems.Thm_Landreman3DEquilibria_field_eq_stretched_axisymmetric
-- name    : Landreman3DEquilibria.field_eq_stretched_axisymmetric
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T18:58:41.889341+00:00
-- url     : https://prove2.me/theorems/486e6f51-e026-4348-ba3b-715e0d4f690d
-- title:
--   $B(x)=A\,B_0(A^{-1}x)$ with $A=\mathrm{diag}(a,b,1)$
-- statement:
--   Let $0<\epsilon<1$, $a=\sqrt{1+\epsilon}$, $b=\sqrt{1-\epsilon}$ and $A=\mathrm{diag}(a,b,1)$. Let $B_0$ denote the axisymmetric member of the family, obtained by setting $\epsilon=0$: in cylindrical coordinates it is the Solov'ev field
--
--   $$B_0=\frac{2Z}{R}e_R+\frac{I(\Psi_0)}{R}e_\phi+(1-R^2)e_Z,\qquad I=\sqrt{1-4\Psi_0},\quad \Psi_0=\frac{(R^2-1)^2}{4}+Z^2 .$$
--
--   Then at every point of $U_\epsilon$ the three-dimensional field is the constant linear stretch of the axisymmetric one,
--
--   $$B(x)=A\,B_0\big(A^{-1}x\big).$$
--
--   This identity is the structural origin of the family: it is why the deformation preserves $\nabla\cdot B=0$ and, because $A$ commutes with $D=\mathrm{diag}(1,1,4)$, why it preserves the tension identity $(B\cdot\nabla)B=-Dx$.
-- source:
--   M. Landreman, Analytic toroidal 3D MHD equilibria and steady Euler flows with invariant surfaces, J. Plasma Phys. (submitted), arXiv:2609.26742v1 (2026), https://arxiv.org/abs/2609.26742 , Section 2, eqs. (2.6) and (2.9)

import Mathlib
import Definitions.Def_landreman_vector_calculus
import Definitions.Def_landreman_integer_iota_family

namespace Landreman3DEquilibria

theorem field_eq_stretched_axisymmetric (e : ℝ) (he : 0 < e) (he1 : e < 1) (x : LVec)
    (hx : x ∈ domainU e) :
    Bfield e x =
      ![aCoef e * Bfield 0 ![x 0 / aCoef e, x 1 / bCoef e, x 2] 0,
        bCoef e * Bfield 0 ![x 0 / aCoef e, x 1 / bCoef e, x 2] 1,
        Bfield 0 ![x 0 / aCoef e, x 1 / bCoef e, x 2] 2] := by sorry

end Landreman3DEquilibria
