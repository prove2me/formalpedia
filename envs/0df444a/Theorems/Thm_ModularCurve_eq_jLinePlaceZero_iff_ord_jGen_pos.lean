-- Prove2me | Theorems.Thm_ModularCurve_eq_jLinePlaceZero_iff_ord_jGen_pos
-- name    : ModularCurve.eq_jLinePlaceZero_iff_ord_jGen_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/12d24bcc-2bc8-5aa1-8bf9-9fb993e8d2f5
-- title:
--   A place of the j-line is v₀ iff ordᵥ(j)>0
-- statement:
--   Let $j(q) \in \mathbb{Q}((q))$ be the Laurent series [`ModularCurve.jq`](def/ModularCurve_X0.html#L157), namely $q^{-1}$ times the rational power series obtained from the integral numerator series of the modular $j$-function, and let $\mathbb{Q}\langle j(q)\rangle$ denote the intermediate field of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by $j(q)$; write [`ModularCurve.jGen`](def/ModularCurve_X0.html#L268) for $j(q)$ regarded as an element of that field. A place of $\mathbb{Q}\langle j(q)\rangle$ over $\mathbb{Q}$ is, in the sense of the project's structure [`AlgebraicCurve.Place`](def/AlgebraicCurve_DivisorClassGroup.html#L22), a valuation subring of $\mathbb{Q}\langle j(q)\rangle$ that contains the image of $\mathbb{Q}$, is not the whole field, and is a principal ideal ring; for such a $v$ and an element $f$, $v.\mathrm{ord}\,f$ is minus the logarithm of the value of $f$ under the associated height-one-spectrum adic valuation. Finally, [`ModularCurve.jLinePlaceZero`](def/ModularCurve_JLinePlaces.html#L54) is the place obtained by transporting, along the isomorphism $\mathbb{Q}(T) \cong \mathbb{Q}\langle j(q)\rangle$ sending $T \mapsto j(q)$ (available since $j(q)$ is transcendental over $\mathbb{Q}$), the finite place of $\mathbb{Q}(T)$ attached to the irreducible polynomial $T - 0$. The theorem asserts: for every place $v$ of $\mathbb{Q}\langle j(q)\rangle$ over $\mathbb{Q}$, one has $v =$ `jLinePlaceZero` if and only if $v.\mathrm{ord}\,(j(q)) > 0$.
--
--   This is the characterisation of the place $j = 0$ of the $j$-line $X(1)_{\mathbb{Q}}$ as the unique place at which the coordinate $j$ has positive order, the other two distinguished places being those at $j = 1728$ and $j = \infty$. It is used by [`ModularCurve.restrict_eq_jLinePlaceZero_iff`](thm.html#ModularCurve.restrict_eq_jLinePlaceZero_iff), which recognises places of the $j$-line obtained by restriction from a larger modular function field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_eq_jLinePlaceZero_iff_ord_jGen_pos.lean

import Mathlib
import Definitions.Def_ModularCurve_JLinePlaces
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IntermediateField AlgebraicCurve

theorem ModularCurve.eq_jLinePlaceZero_iff_ord_jGen_pos (v : AlgebraicCurve.Place ℚ ↥ℚ⟮ModularCurve.jq⟯) :
    v = ModularCurve.jLinePlaceZero ↔ 0 < v.ord ModularCurve.jGen := by sorry
