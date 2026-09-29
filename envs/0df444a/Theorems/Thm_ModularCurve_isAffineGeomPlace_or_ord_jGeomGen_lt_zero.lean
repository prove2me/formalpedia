-- Prove2me | Theorems.Thm_ModularCurve_isAffineGeomPlace_or_ord_jGeomGen_lt_zero
-- name    : ModularCurve.isAffineGeomPlace_or_ord_jGeomGen_lt_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/21ce2b97-e611-54bc-8de7-b5d81ed9f35a
-- title:
--   Every place is affine or a pole of ̄ j
-- statement:
--   Let $K$ be a field and $N$ a non-zero natural number, and let $F = K(\,\overline{j},\overline{j}_N\,)$ denote `modularFunctionFieldC K N`, the intermediate field of the Laurent series field $K((q))$ generated over $K$ by the two series $q^{-1}\cdot\mathrm{jNum}$ (the element `jGeomGen K N`, written $\overline{j}$) and its $q\mapsto q^{N}$ substitute `jqNModC K N` (the element `jNGeomGen K N`, written $\overline{j}_N$). Let $w$ be a place of $F$ over $K$ in the sense of [`AlgebraicCurve.Place`](def/AlgebraicCurve_DivisorClassGroup.html#L22), that is, a valuation subring $\mathcal{O}_w \subseteq F$ which contains the image of $K$, is not all of $F$, and is a principal ideal ring. The assertion is the dichotomy: either `IsAffineGeomPlace K N w` holds, i.e. both $\overline{j}$ and $\overline{j}_N$ lie in $\mathcal{O}_w$; or $\operatorname{ord}_w(\overline{j}) < 0$, where $\operatorname{ord}_w$ is minus the logarithm of the $\mathbb{Z}^{m0}$-valued adic valuation of $F$ attached to the height-one prime of $\mathcal{O}_w$. The two alternatives are not asserted to be exclusive.
--
--   This is the classical statement that a place of the function field of the modular curve of level $N$ is either a point of the affine $(j,j_N)$-model or a cusp, where $\overline{j}$ has a pole. It is the basic dichotomy used throughout the analysis of places of modular function fields in this development, and is invoked by the various results locating places on special fibres and on the Deligne–Rapoport type models at level $N$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isAffineGeomPlace_or_ord_jGeomGen_lt_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.isAffineGeomPlace_or_ord_jGeomGen_lt_zero
    (K : Type*) [Field K] (N : ℕ) [NeZero N]
    (w : AlgebraicCurve.Place K ↥(modularFunctionFieldC K N)) :
    IsAffineGeomPlace K N w ∨ w.ord (jGeomGen K N) < 0 := by sorry
