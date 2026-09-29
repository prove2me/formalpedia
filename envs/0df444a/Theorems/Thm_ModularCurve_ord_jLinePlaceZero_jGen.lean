-- Prove2me | Theorems.Thm_ModularCurve_ord_jLinePlaceZero_jGen
-- name    : ModularCurve.ord_jLinePlaceZero_jGen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/c5bdae23-0985-575a-b6e5-8d6aa05af46a
-- title:
--   j is a uniformiser at the place j=0
-- statement:
--   Here $\mathbb{Q}\langle j\rangle = \mathbb{Q}\!\left(\mathrm{jq}\right)$ denotes the simple extension of $\mathbb{Q}$ generated inside the relevant Laurent/power series field by the $q$-expansion $\mathrm{jq}$ of the modular $j$-invariant, and [`ModularCurve.jGen`](def/ModularCurve_X0.html#L268) is that generator viewed as an element of $\mathbb{Q}\langle j\rangle$. A place of $\mathbb{Q}\langle j\rangle$ over $\mathbb{Q}$, in the sense of the project's structure `Place`, is a valuation subring of $\mathbb{Q}\langle j\rangle$ that contains the image of $\mathbb{Q}$, is not the whole field, and is a principal ideal ring; for such a place $v$ and $f$ in the field, $v.\mathrm{ord}(f)$ is minus the logarithm of the value of $f$ under the adic valuation attached to the height-one prime of the valuation ring, i.e. the integer exponent with which the maximal ideal divides $f$. The place [`ModularCurve.jLinePlaceZero`](def/ModularCurve_JLinePlaces.html#L54) is obtained by transporting, along the isomorphism [`ModularCurve.jLineRingEquiv`](def/ModularCurve_JLinePlaces.html#L36) $:\ \mathrm{RatFunc}\,\mathbb{Q} \xrightarrow{\ \sim\ } \mathbb{Q}\langle j\rangle$ sending the variable to $\mathrm{jq}$ (and fixing $\mathbb{Q}$), the finite place of $\mathbb{Q}(T)$ cut out by the irreducible polynomial $T-0$. The assertion is that the order of $\mathrm{jq}$ at this place equals $1$; that is, $j$ is a uniformiser at the place $j=0$ of the $j$-line.
--
--   This records the elementary but needed fact that the rational function $j$ has a simple zero at the point $j=0$ of the $j$-line $X(1)_{\mathbb{Q}}$, the place being one of the three distinguished places $j=0,1728,\infty$. It is used by [`ModularCurve.ramificationIndex_eq_ord_of_restrict_eq_jLinePlaceZero`](thm.html#ModularCurve.ramificationIndex_eq_ord_of_restrict_eq_jLinePlaceZero), where ramification indices of places of modular function fields above $j=0$ are computed as orders of $j$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ord_jLinePlaceZero_jGen.lean

import Mathlib
import Definitions.Def_ModularCurve_JLinePlaces
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IntermediateField AlgebraicCurve

theorem ModularCurve.ord_jLinePlaceZero_jGen : ModularCurve.jLinePlaceZero.ord ModularCurve.jGen = 1 := by sorry
