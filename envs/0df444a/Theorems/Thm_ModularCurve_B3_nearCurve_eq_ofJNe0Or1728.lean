-- Prove2me | Theorems.Thm_ModularCurve_B3_nearCurve_eq_ofJNe0Or1728
-- name    : ModularCurve.B3.nearCurve_eq_ofJNe0Or1728
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/7de599c8-4815-5760-8ccf-ef715d7fdc66
-- title:
--   The near-curve is the explicit model at j₀+s
-- statement:
--   Let $\overline{\mathbb{Q}}$ denote the algebraic closure of $\mathbb{Q}$ (the abbreviation `Qbar`), and let $H$ be the field of Hahn series with rational exponents and coefficients in $\overline{\mathbb{Q}}$, whose uniformiser $s$ is the series `HahnSeries.single (1 : ℚ) (1 : Qbar)` supported in exponent $1$ with coefficient $1$. For an element $j_0$ of $\overline{\mathbb{Q}}$, the project writes `jNear j₀` for the Hahn series $j_0 + s$, that is the constant series `HahnSeries.C j₀` plus the uniformiser, and `nearCurve j₀` for `WeierstrassCurve.ofJ (jNear j₀)`, Mathlib's Weierstrass curve over $H$ with prescribed $j$-invariant $j_0 + s$, which is defined by a case distinction according as the prescribed invariant is $0$, is $1728$, or is neither. The theorem asserts, for every $j_0$, the equality of Weierstrass curves over $H$
--   $$\mathrm{nearCurve}(j_0) = \mathrm{ofJNe0Or1728}(j_0+s),$$
--   where the right-hand side is Mathlib's explicit five-tuple of coefficients $a_1 = j-1728$, $a_2 = a_3 = 0$, $a_4 = -36(j-1728)^3$, $a_6 = -(j-1728)^5$ evaluated at $j = j_0 + s$. In other words, the case distinction in `WeierstrassCurve.ofJ` always resolves to the generic branch at the argument $j_0+s$, no hypothesis on $j_0$ being required.
--
--   This is the statement that the one-parameter deformation $j_0+s$ of a $j$-value never meets the two exceptional points $j=0$, $j=1728$ of the $j$-line, so that the curve attached to it is given by the explicit global Weierstrass equation of the universal curve over $\mathbb{A}^1_j \setminus \{0,1728\}$. It is what makes the coefficients of the near-curve, and hence their orders of vanishing in $s$, available as explicit polynomials in $j_0+s$ in the subsequent study of reduction and of torsion points over $H$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_B3_nearCurve_eq_ofJNe0Or1728.lean

import Definitions.Def_ModularCurve_SpecialisationVocab
import Definitions.Def_ModularCurve_TatePoint

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve.TatePoint

theorem ModularCurve.B3.nearCurve_eq_ofJNe0Or1728 (j₀ : Qbar) :
    nearCurve j₀ = WeierstrassCurve.ofJNe0Or1728 (jNear j₀) := by sorry
