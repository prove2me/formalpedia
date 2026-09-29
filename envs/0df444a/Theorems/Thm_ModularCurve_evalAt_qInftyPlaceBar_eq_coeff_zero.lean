-- Prove2me | Theorems.Thm_ModularCurve_evalAt_qInftyPlaceBar_eq_coeff_zero
-- name    : ModularCurve.evalAt_qInftyPlaceBar_eq_coeff_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/5a06ea43-400c-5adf-9d54-570fbbe03dd2
-- title:
--   Value at the q-adic place is the constant coefficient
-- statement:
--   Let $L$ be a field and let $F$ be an intermediate field of the extension $L \subseteq L(\!(q)\!)$ of the Laurent series field, so each $f \in F$ has an underlying Laurent series $qSeriesBar\,L\,F\,f$ with a $q$-order in $\mathbb{Z} \cup \{\infty\}$. Assume $h$: some $j \in F$ has Laurent series of order exactly $-1$. This hypothesis makes [`ModularCurve.qInftyPlaceBar L F h`](def/ModularCurve_QAdicPlace.html#L300) a `Place L F`, that is, a valuation subring of $F$ which contains the image of $L$, is not all of $F$, and is a principal ideal ring; its underlying valuation subring is [`ModularCurve.qIntegersBar L F`](def/ModularCurve_QAdicPlace.html#L128), the set of $f \in F$ whose Laurent series has order $\ge 0$. Let $f \in F$ satisfy $0 \le \operatorname{ord}(qSeriesBar\,L\,F\,f)$. Then the evaluation of $f$ at this place — defined, for $f$ in the valuation subring, as the image of the residue class of $f$ under a chosen left inverse of the structure map $L \to$ residue field, and as $0$ otherwise — equals the coefficient of $q^0$ in the Laurent series of $f$.
--
--   This is the algebraic form of the statement that a function regular at the cusp $\infty$ takes there the constant term $a_0$ of its $q$-expansion, the normalisation used when evaluating functions and units at the cusp. It is used in the construction of suitable centred local data for integral models of modular curves of full level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_evalAt_qInftyPlaceBar_eq_coeff_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve AlgebraicCurve

theorem ModularCurve.evalAt_qInftyPlaceBar_eq_coeff_zero (L : Type*) [Field L]
    {F : IntermediateField L (LaurentSeries L)} (h : ∃ j : F, (qSeriesBar L F j).order = -1)
    (f : F) (hf : 0 ≤ (qSeriesBar L F f).order) :
    (qInftyPlaceBar L F h).evalAt f = (qSeriesBar L F f).coeff 0 := by sorry
