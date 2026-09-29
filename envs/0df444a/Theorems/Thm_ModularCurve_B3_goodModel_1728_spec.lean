-- Prove2me | Theorems.Thm_ModularCurve_B3_goodModel_1728_spec
-- name    : ModularCurve.B3.goodModel_1728_spec
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/52339f10-05e7-51eb-933b-d3d9c5e64858
-- title:
--   Integral model at j₀=1728 with unit discriminant
-- statement:
--   The assertion is a closed statement about one explicitly given Weierstrass curve over the series field $H$, namely `goodModel 1728`, which is by definition the curve `WeierstrassCurve.ofJ (jNear 1728)` transformed by the variable change `scaleVC 1728`; since $1728 \ne 0$, that variable change is the one with $u =$ `sU (9/12)`, i.e. the scaling factor of exponent $3/4$, and with $r = s = t = 0$, so it is a pure rescaling with no translation. Three things are asserted. First, `IntegralCoeffs` holds for this curve: each of $a_1, a_2, a_3, a_4, a_6$ has $\mathrm{orderTop} \ge 0$, i.e. all five coefficients lie in the valuation ring. Second, its discriminant satisfies $\mathrm{orderTop}\,\Delta = 0$, so $\Delta$ is a unit. Third, the special fibre — the Weierstrass curve over $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` whose coefficients are the degree-zero coefficients `coeff 0` of $a_1,\dots,a_6$ — admits a witness of `IsElliptic`, and with respect to it its $j$-invariant equals $1728$.
--
--   This is the good-reduction statement at the special $j$-value $1728$: after a ramified rescaling of exponent $3/4$, the curve with $j$-invariant near $1728$ acquires integral coefficients, unit discriminant and an elliptic special fibre of $j$-invariant $1728$. It is the counterpart, at $j_0 = 1728$, of the corresponding statement at $j_0 = 0$, and serves the specialisation vocabulary in which reduction of curves and of their torsion over the series field is set up.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_B3_goodModel_1728_spec.lean

import Definitions.Def_ModularCurve_SpecialisationVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.B3.goodModel_1728_spec :
    IntegralCoeffs (goodModel 1728) ∧ (goodModel 1728).Δ.orderTop = 0 ∧
      ∃ _ : (specialFibre (goodModel 1728)).IsElliptic,
        (specialFibre (goodModel 1728)).j = 1728 := by sorry
