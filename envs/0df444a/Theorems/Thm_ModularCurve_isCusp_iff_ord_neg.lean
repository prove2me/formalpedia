-- Prove2me | Theorems.Thm_ModularCurve_isCusp_iff_ord_neg
-- name    : ModularCurve.isCusp_iff_ord_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/6a851602-4ebf-5f58-93a9-0ac000883613
-- title:
--   Cusps are the places where j has negative order
-- statement:
--   Let $K$ and $E$ be fields with $E$ a $K$-algebra, let $j \in E$, and let $v$ be a place of $E$ over $K$, that is, a valuation subring `v.toValuationSubring` of $E$ which contains the image of $K$ under the structure map, is not all of $E$, and is a principal ideal ring. The assertion is the equivalence of two conditions on $j$: the predicate `IsCusp j v`, which by definition says that $j$ does not belong to `v.toValuationSubring`, holds if and only if $v.\mathrm{ord}(j) < 0$, where $\mathrm{ord}$ is the integer-valued order function attached to $v$, namely $\mathrm{ord}(f) = -\log$ of the value of $f$ under the adic valuation of the height-one prime of `v.toValuationSubring` determined by $v$ (with values in $\mathbb{Z}^{m0}$). Thus being a cusp for $j$ in the sense of this development is exactly the condition that $j$ has a pole at $v$. In particular, for $j = 0$ both sides fail, since $0$ lies in every valuation subring and $\mathrm{ord}(0) = 0$ by convention.
--
--   This is the translation between the membership formulation of a cusp, as a place at which the modular function $j$ fails to be integral, and the numerical formulation in terms of the order of vanishing, so that cusps can be handled by divisor-theoretic computations. It is used throughout the treatment of places of modular curves, for instance in the estimates on $\mathrm{ord}$ of $j$ in characteristic $p$ models and in the specialisation and height computations for the $j$-line.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isCusp_iff_ord_neg.lean

import Definitions.Def_ModularCurve_QAdicPlace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.isCusp_iff_ord_neg {K : Type*} {E : Type*} [Field K] [Field E] [Algebra K E] (j : E) (v : Place K E) : IsCusp j v ↔ v.ord j < 0 := by sorry
