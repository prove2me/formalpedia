-- Prove2me | Theorems.Thm_ModularCurve_B3_isElliptic_specialFibre
-- name    : ModularCurve.B3.isElliptic_specialFibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/626aca83-fa00-519e-b5e3-231786751ad9
-- title:
--   Unit discriminant gives an elliptic special fibre
-- statement:
--   Let $H$ be the Hahn series field with coefficients in $\bar{\mathbb{Q}} =$ `Qbar` $=$ `AlgebraicClosure ℚ`, and let $W$ be a Weierstrass curve over $H$, given by coefficients $a_1,a_2,a_3,a_4,a_6 \in H$. Assume first `IntegralCoeffs W`, that is, each of the five coefficients has $\mathrm{orderTop} \ge 0$, so no coefficient has a term of negative exponent; and assume second that the discriminant $\Delta$ of $W$ satisfies $\mathrm{orderTop}(\Delta) = 0$, i.e. $\Delta$ is nonzero, has no terms of negative exponent, and its constant term is nonzero. The conclusion is that `specialFibre W`, the Weierstrass curve over $\bar{\mathbb{Q}}$ whose coefficients are the constant terms $a_1(0), a_2(0), a_3(0), a_4(0), a_6(0)$ of those of $W$, satisfies `IsElliptic`: its discriminant is a unit of $\bar{\mathbb{Q}}$, equivalently nonzero, so the plane cubic it defines is nonsingular.
--
--   This is the good-reduction criterion in its model-theoretic form: an integral Weierstrass model whose discriminant is a unit specialises to an elliptic curve over the residue field. It is the step that allows the special fibre to be treated as an elliptic curve, with a group of points and a torsion theory, in the specialisation vocabulary used for the Tate point construction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_B3_isElliptic_specialFibre.lean

import Definitions.Def_ModularCurve_SpecialisationVocab
import Definitions.Def_ModularCurve_TatePoint

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve.TatePoint
open scoped Classical

theorem ModularCurve.B3.isElliptic_specialFibre (W : WeierstrassCurve H)
    (hW : IntegralCoeffs W) (hΔ : W.Δ.orderTop = 0) : (specialFibre W).IsElliptic := by sorry
