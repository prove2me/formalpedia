-- Prove2me | Theorems.Thm_ModularCurve_deg_cuspZeroBar
-- name    : ModularCurve.deg_cuspZeroBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/f1ded983-c4d2-5f24-ab67-c3cea05ab025
-- title:
--   The cusp ̄ 0 has degree one
-- statement:
--   Let $N$ be a natural number, assumed nonzero. Work with $\bar{\mathbb{Q}} =$ `AlgebraicClosure ℚ` and with the field `modularFunctionFieldBar N`, the base change to $\bar{\mathbb{Q}}$ of the full level-$N$ modular function field, realised as an intermediate field of the Laurent series field $\bar{\mathbb{Q}}((q))$. On such a field extension, a `Place` consists of a valuation subring of the big field which contains the image of the base field, is not the whole field, and is a principal ideal ring; its degree `Place.deg` is the $\bar{\mathbb{Q}}$-dimension `Module.finrank` of the residue field of that valuation subring. The place `cuspInftyBar N` is the $q$-expansion place at infinity of `modularFunctionFieldBar N`, normalised by the element coming from $j(q)$ and its order, and `cuspZeroBar N` is the translate of `cuspInftyBar N` under the pointwise action of `frickeInvolutionBar N`, the $\bar{\mathbb{Q}}$-algebra automorphism of `modularFunctionFieldBar N` induced by the Fricke involution of the full modular function field. The assertion is that $(\mathrm{cuspZeroBar}\ N).\deg = 1$: the cusp $\bar 0$ is a rational point, its residue field being $\bar{\mathbb{Q}}$ itself.
--
--   This records that the second distinguished cusp of the modular curve of level $N$ over $\bar{\mathbb{Q}}$, obtained from the cusp at infinity by the Fricke involution, has residue degree one. It feeds the computations with cuspidal divisors and the Hecke action on them, such as [`ModularCurve.heckeDivBar_cuspidalDivisor_of_prime`](thm.html#ModularCurve.heckeDivBar_cuspidalDivisor_of_prime) and [`ModularCurve.heckeAlphaBar_frickeInvolutionBar_sq`](thm.html#ModularCurve.heckeAlphaBar_frickeInvolutionBar_sq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_deg_cuspZeroBar.lean

import Definitions.Def_ModularCurve_CuspidalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.deg_cuspZeroBar (N : ℕ) [NeZero N] : (cuspZeroBar N).deg = 1 := by sorry
