-- Prove2me | Theorems.Thm_ModularCurve_deg_qInftyPlaceBar
-- name    : ModularCurve.deg_qInftyPlaceBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/dbab1825-c255-5b5e-a15d-7558afab166e
-- title:
--   The q-adic place at infinity has degree one
-- statement:
--   Let $L$ be a field and let $F$ be an intermediate field of the extension $L((q))/L$ of Laurent series over $L$, and assume there is an element $j \in F$ whose underlying Laurent series $\mathrm{qSeriesBar}\,L\,F\,j$ has order exactly $-1$. Under this hypothesis `qInftyPlaceBar L F h` is the place of $F$ over $L$ whose valuation subring is `qIntegersBar L F`, the subring of those $f \in F$ whose underlying Laurent series has non-negative order; the hypothesis $h$ supplies the witness used to see that this subring is a proper subring of $F$ and is a principal ideal ring, and the image of $L$ in $F$ lies in it. The assertion is that the degree of this place is $1$, that is, that the residue field of the local ring `qIntegersBar L F`, viewed as an $L$-algebra, has dimension $1$ as an $L$-vector space. Equivalently, the structure map $L \to$ (residue field) is an isomorphism.
--
--   The place in question is the cusp $\infty$ of the $q$-expansion picture of a modular function field, and the statement records that it is a rational point, i.e. a degree-one place with residue field the constant field $L$. It is used in the proofs that the constants of the various modular function fields constructed in the project coincide with the base field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_deg_qInftyPlaceBar.lean

import Definitions.Def_ModularCurve_QAdicPlace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.deg_qInftyPlaceBar (L : Type*) [Field L] {F : IntermediateField L (LaurentSeries L)} (h : ∃ j : F, (qSeriesBar L F j).order = -1) : (qInftyPlaceBar L F h).deg = 1 := by sorry
