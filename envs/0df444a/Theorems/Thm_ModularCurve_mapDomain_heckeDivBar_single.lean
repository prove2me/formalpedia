-- Prove2me | Theorems.Thm_ModularCurve_mapDomain_heckeDivBar_single
-- name    : ModularCurve.mapDomain_heckeDivBar_single
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/9fd55939-1572-5af6-b5a7-b6821cf6cc57
-- title:
--   Hecke divisor of a single place, transported along sp
-- statement:
--   Let $L$ be a field with a $\mathbb{Q}$-algebra structure and let $N,\ell$ be nonzero natural numbers. Write $F_M =$ `laurentBaseChange L (modularFunctionFieldFull M)`, the intermediate field of $L((q))$ generated over $L$ by the coefficientwise image of the field `modularFunctionFieldFull M` $\subseteq \mathbb{Q}((q))$, itself the $\mathbb{Q}$-adjunction of the divisor expansions of level $M$. Assume the two degeneracy $L$-algebra maps $\alpha =$ `heckeAlphaBar L N ℓ` and $\beta =$ `heckeBetaBar L N ℓ` from $F_N$ to $F_{N\ell}$ are integral (hypotheses `hα`, `hβ`), and that $F_{N\ell}$ has principal divisors over $L$, i.e. every nonzero $f$ has a degree-zero divisor recording its orders at all places. Let $k \subseteq F'$ be fields, let $\mathrm{sp}$ be an arbitrary function from the places of $F_N$ over $L$ (valuation subrings containing $L$, proper, and principal ideal rings) to the places of $F'$ over $k$, let $v$ be such a place of $F_N$ and $n \in \mathbb{Z}$. Then the image under `Finsupp.mapDomain sp` of $\mathrm{heckeDivBar}(n\,v) = \alpha_*\beta^*(n\,v)$ equals $\sum_{W} \mathrm{single}\,(\mathrm{sp}(W|_\alpha))\,\bigl(n\,e_\beta(W)\,f_\alpha(W)\bigr)$, the sum over the finite $\beta$-fibre of $v$.
--
--   This is the prime-divisor formula for the Hecke correspondence $\alpha_*\beta^*$ at level $N$, composed with an arbitrary relabelling of places; it is the shape in which the divisor of a single place is compared with an operator on a special fibre. It is used by the results computing the specialisation of `heckeDivBar` along a chart of the characteristic-$p$ fibre model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_mapDomain_heckeDivBar_single.lean

import Definitions.Def_ModularCurve_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve

theorem ModularCurve.mapDomain_heckeDivBar_single {L : Type*} [Field L] [Algebra ℚ L] {N ℓ : ℕ} [NeZero N] [NeZero ℓ] (hα : HeckeAlphaBarIntegral L N ℓ) (hβ : HeckeBetaBarIntegral L N ℓ) [HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull (N * ℓ)))] {k F' : Type*} [Field k] [Field F'] [Algebra k F'] (sp : Place L (laurentBaseChange L (modularFunctionFieldFull N)) → Place k F') (v : Place L (laurentBaseChange L (modularFunctionFieldFull N))) (n : ℤ) :
    Finsupp.mapDomain sp (heckeDivBar hα hβ (Finsupp.single v n)) = ∑ W ∈ Place.fiberAlong (heckeBetaBar L N ℓ) hβ v, Finsupp.single (sp (W.restrictAlong (heckeAlphaBar L N ℓ) hα)) (n * (W.ramificationIndexAlong (heckeBetaBar L N ℓ) : ℤ) * (W.inertiaDegAlong (heckeAlphaBar L N ℓ) hα : ℤ)) := by sorry
