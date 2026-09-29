-- Prove2me | Theorems.Thm_ModularCurve_eq_jLinePlace1728_iff_ord_jGen_sub_pos
-- name    : ModularCurve.eq_jLinePlace1728_iff_ord_jGen_sub_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/bbd97c03-8715-591b-8750-ab5ad0a78c74
-- title:
--   A place of the j-line is v₁₇₂₈ iff ordᵥ(j-1728)>0
-- statement:
--   Let $j$ denote the Laurent series [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) over $\mathbb{Q}$, namely $q^{-1}$ times the power series `jNumQ`, let $\mathbb{Q}\langle j\rangle = \mathbb{Q}\langle\!\langle\mathrm{jq}\rangle\!\rangle$ be the subfield of the Laurent series field generated over $\mathbb{Q}$ by $j$, and let `jGen` be $j$ regarded as an element of that field. For a place $v$ of $\mathbb{Q}\langle j\rangle$ over $\mathbb{Q}$ — that is, a valuation subring of $\mathbb{Q}\langle j\rangle$ containing the image of $\mathbb{Q}$, different from the whole field, and a principal ideal ring — the statement asserts the equivalence of: (i) $v$ equals [`ModularCurve.jLinePlace1728`](def/ModularCurve_JLinePlaces.html#L50), the place obtained by transporting along the ring isomorphism `jLineRingEquiv : RatFunc ℚ ≃+* ℚ⟮jq⟯` (which carries the variable to $j$ and fixes $\mathbb{Q}$) the finite place `placeOfPoint ℚ 1728` of $\mathbb{Q}(T)$ attached to the irreducible polynomial $T - 1728$; and (ii) $0 < v.\mathrm{ord}(\mathrm{jGen} - 1728)$, where $v.\mathrm{ord}$ is minus the logarithm of the $\mathbb{Z}^{m0}$-valued adic valuation attached to the height-one prime of $v$, so that the condition says $j - 1728$ has a zero at $v$.
--
--   This identifies the place $j = 1728$ of the $j$-line over $\mathbb{Q}$ by the vanishing of $j - 1728$, one of the three distinguished places ($j = 0$, $j = 1728$, $j = \infty$) of the rational function field $\mathbb{Q}(j)$. It is used via [`ModularCurve.restrict_eq_jLinePlace1728_iff`](thm.html#ModularCurve.restrict_eq_jLinePlace1728_iff) to recognise, by an order condition, those places of a modular curve lying over $j = 1728$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_eq_jLinePlace1728_iff_ord_jGen_sub_pos.lean

import Mathlib
import Definitions.Def_ModularCurve_JLinePlaces
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IntermediateField AlgebraicCurve

theorem ModularCurve.eq_jLinePlace1728_iff_ord_jGen_sub_pos (v : AlgebraicCurve.Place ℚ ↥ℚ⟮ModularCurve.jq⟯) :
    v = ModularCurve.jLinePlace1728 ↔ 0 < v.ord (ModularCurve.jGen - 1728) := by sorry
