-- Prove2me | Theorems.Thm_ModularCurve_UVCrossingModel_repGaussOrder_normalForm_eq_iInf_termOrder
-- name    : ModularCurve.UVCrossingModel.repGaussOrder_normalForm_eq_iInf_termOrder
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/23981f13-546a-5f52-920c-085ca3aae234
-- title:
--   Gauss order of a normal form equals infimum of term orders
-- statement:
--   Let $W$ be a commutative ring, let $v : W \to \mathbb{N}\cup\{\infty\}$ be an arbitrary function subject only to $v(0) = \infty$, let $E, t$ be natural numbers, and let $ab = (a,b)$ be a pair of one-variable power series over $W$ whose second component has vanishing constant coefficient, $b(0) = 0$. Form the two-variable power series $\mathrm{inU}\,a + \mathrm{inV}\,b$ in $W[[X_0,X_1]]$, where $\mathrm{inU}\,a$ has coefficient $a_{d_0}$ at a multi-index $d$ with $d_1 = 0$ and $0$ otherwise, and $\mathrm{inV}\,b$ has coefficient $b_{d_1}$ at $d$ with $d_0 = 0$ and $0$ otherwise. The assertion is an equality in $\mathbb{N}\cup\{\infty\}$ between two infima: on the left, $\mathrm{repGaussOrder}$ of this series, namely $\inf_{d}\bigl(v(\mathrm{coeff}_d(\mathrm{inU}\,a + \mathrm{inV}\,b)) + d_0 t + d_1 (E - t)\bigr)$ over all $d \in (\mathrm{Fin}\,2 \to_0 \mathbb{N})$, with $E - t$ truncated subtraction of naturals; on the right, the infimum over $n \in \mathbb{Z}$ of $\mathrm{termOrder}\,v\,E\,t\,ab\,n$, which for $n = i \ge 0$ is $v(a_i) + i\,t$ and for $n = -(j+1)$ with $j \ge 0$ is $v(b_{j+1}) + (j+1)(E-t)$.
--
--   This identifies the Gauss order at weight $(t, E-t)$ of an element of the crossing model $W[[X_0,X_1]]/(X_0X_1 - \pi)$, computed from the representative $a(U) + b(V)$ in normal form, with the infimum of the weighted orders of its terms indexed by $\mathbb{Z}$ in Laurent fashion. It is the bridge through which the slope computations for prolongation tuples in the place-specialisation theory evaluate Gauss orders term by term; the hypothesis $v(0) = \infty$ ensures that the off-axis coefficients, which vanish, do not lower the infimum, and $b(0) = 0$ prevents the constant term from being counted twice.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_UVCrossingModel_repGaussOrder_normalForm_eq_iInf_termOrder.lean

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_ModularCurve_UVCrossingGaussOrder
import Definitions.Def_ModularCurve_UVCrossingDominantIndices

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open ModularCurve ModularCurve.UVCrossingModel IsLocalRing

theorem ModularCurve.UVCrossingModel.repGaussOrder_normalForm_eq_iInf_termOrder
    {W : Type u} [CommRing W] (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E t : ℕ) (ab : PowerSeries W × PowerSeries W)
    (hb : PowerSeries.constantCoeff ab.2 = 0) :
    repGaussOrder v E t (inU ab.1 + inV ab.2) = ⨅ n : ℤ, termOrder v E t ab n := by sorry
