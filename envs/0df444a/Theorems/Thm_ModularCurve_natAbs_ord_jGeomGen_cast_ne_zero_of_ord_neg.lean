-- Prove2me | Theorems.Thm_ModularCurve_natAbs_ord_jGeomGen_cast_ne_zero_of_ord_neg
-- name    : ModularCurve.natAbs_ord_jGeomGen_cast_ne_zero_of_ord_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/455e513e-5946-536d-9882-795dfe72a9ea
-- title:
--   Pole order of jmath̄ at a place is nonzero in K
-- statement:
--   Let $p$ be a prime, let $K$ be an algebraically closed field of characteristic $p$, and let $N$ be a positive natural number whose image $(N : K)$ is nonzero. Inside the field $\mathrm{LaurentSeries}\,K$ of formal Laurent series over $K$, consider the intermediate field $F_N = \mathrm{modularFunctionFieldC}\,K\,N$ obtained by adjoining to $K$ the two series $\mathrm{jqModC}\,K = q^{-1}\cdot\iota(\mathrm{jNum})$ (the Hahn series $\mathrm{single}(-1,1)$ times the power series $\mathrm{jNum}$ with coefficients reduced into $K$) and its $N$-fold substitution $\mathrm{jqNModC}\,K\,N = \mathrm{qExpand}\,K\,N(\mathrm{jqModC}\,K)$. Let $w$ be a place of $F_N$ over $K$, that is, a valuation subring of $F_N$ containing the image of $K$, different from $F_N$ itself and a principal ideal ring; let $w.\mathrm{ord}$ denote minus the logarithm of the associated adic valuation. Write $\mathrm{jGeomGen}\,K\,N$ for the element $\mathrm{jqModC}\,K$ of $F_N$. Assume $w.\mathrm{ord}(\mathrm{jGeomGen}\,K\,N) < 0$. The conclusion is that the natural number $|w.\mathrm{ord}(\mathrm{jGeomGen}\,K\,N)|$, cast into $K$, is nonzero.
--
--   Classically the places of the function field of $X_0(N)$ at which $\bar\jmath$ has a pole are the cusps, and the pole order there is the cusp width, a divisor of $N$; the assertion is that this width is prime to the characteristic when $N$ is invertible in $K$. It feeds the tameness bookkeeping at the cusps, and is used in the analysis of orders of $\mathrm{ord}$-values attached to $\mathrm{jqModC}$ and $\mathrm{jqNModC}$ and in the Hecke-operator computations on the special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_natAbs_ord_jGeomGen_cast_ne_zero_of_ord_neg.lean

import Mathlib
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicCurve ModularCurve

theorem ModularCurve.natAbs_ord_jGeomGen_cast_ne_zero_of_ord_neg
    (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] [IsAlgClosed K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)
    (w : AlgebraicCurve.Place K ↥(modularFunctionFieldC K N)) (hw : w.ord (jGeomGen K N) < 0) :
    (((w.ord (jGeomGen K N)).natAbs : ℕ) : K) ≠ 0 := by sorry
