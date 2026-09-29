-- Prove2me | Theorems.Thm_ModularCurve_evalAt_jNGeomGen_eq_zero_of_mem_ssPlaces_of_lt_five
-- name    : ModularCurve.evalAt_jNGeomGen_eq_zero_of_mem_ssPlaces_of_lt_five
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/d3c9214a-4c9a-54f4-a642-614317364228
-- title:
--   Vanishing of the second j-value at supersingular places for q<5
-- statement:
--   Let $q$ be a prime, $N$ a nonzero natural number, and $K$ an algebraically closed field of characteristic $q$ equipped with decidable equality. Assume $q < 5$ and $q \nmid N$. Let $w$ be a place of the level-$N$ modular function field $\mathtt{modularFunctionFieldC}\,K\,N$ over $K$, that is, the subfield of the Laurent series field $K((q))$ generated over $K$ by the Laurent series $\mathtt{jqModC}\,K$ (the $q$-expansion of $j$, namely $q^{-1}$ times the power series `jNum` with coefficients mapped into $K$) and by $\mathtt{jqNModC}\,K\,N = \mathtt{qExpand}\,K\,N(\mathtt{jqModC}\,K)$; a place is a valuation subring of this field, proper, containing $\operatorname{algebraMap} K$ of all of $K$, and a principal ideal ring. Suppose $w \in \mathtt{ssPlaces}\,q\,N\,K$, i.e. $w$ is rational, satisfies the predicate `IsAffineGeomPlace K N`, and $w.\mathtt{evalAt}(\mathtt{jGeomGen}\,K\,N)$ lies in the set `ssJSet q K`. Then $w.\mathtt{evalAt}(\mathtt{jNGeomGen}\,K\,N) = 0$, where `jNGeomGen K N` is the element $\mathtt{jqNModC}\,K\,N$ of that field and $\mathtt{evalAt}$ sends an element of the valuation subring to the preimage in $K$ of its residue, and sends any element outside the valuation subring to $0$.
--
--   This is the characteristic $2$ and $3$ form of the classical fact that the only supersingular $j$-invariant in those characteristics is $0$, combined with the stability of supersingularity under isogeny: at a supersingular place of the level-$N$ modular function field the second coordinate, the $j$-invariant of the target of the associated cyclic $N$-isogeny, also vanishes. Nothing is asserted at cusps or at ordinary places; the result feeds the comparison of the two ramification readings of a supersingular place in [`ModularCurve.placeRamificationJ_mul_jWidthChar_evalAt_jNGeomGen_eq_of_mem_ssPlaces`](thm.html#ModularCurve.placeRamificationJ_mul_jWidthChar_evalAt_jNGeomGen_eq_of_mem_ssPlaces).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_evalAt_jNGeomGen_eq_zero_of_mem_ssPlaces_of_lt_five.lean

import Definitions.Def_ModularCurve_SupersingularNodePlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option Elab.async false
set_option autoImplicit false
open AlgebraicCurve ModularCurve

theorem ModularCurve.evalAt_jNGeomGen_eq_zero_of_mem_ssPlaces_of_lt_five
    {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N]
    {K : Type*} [Field K] [CharP K q] [IsAlgClosed K] [DecidableEq K]
    (hqlt5 : q < 5) (hqN : ¬ q ∣ N)
    {w : Place K (modularFunctionFieldC K N)} (hw : w ∈ ssPlaces q N K) :
    w.evalAt (jNGeomGen K N) = 0 := by sorry
