-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_valuation_evalAt_lt_one_iff_mem_maximalIdeal
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.valuation_evalAt_lt_one_iff_mem_maximalIdeal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/3b7cd36e-310c-5481-b9e3-0ee2723cebf7
-- title:
--   Valuation of values less than one detects the maximal ideal
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a nonzero level $N$, a field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$; fix modular polynomial data `data` for $q$ together with the Kronecker congruence `hKr` for it, the integrality hypotheses $h\alpha$, $h\beta$ asserting that the ring maps underlying `heckeAlphaBar` and `heckeBetaBar` over $\overline{\mathbb Q}$ at level $N$ and index $q$ are integral, and a place specialization $P$ for these data. Let $R$ be a prolongation tuple for $P$, let $K$ be an intermediate field of $\overline{\mathbb Q}/\mathbb Q$ and let $w$ be a place of $k$-modular function field `modularFunctionFieldC k N`, and assume the subring $B = R.\mathrm{nodeIntegersOver}\,K\,w$ of `modularFunctionFieldBar (N * q)` — consisting of those $f$ lying in $R.\mathrm{nodeIntegers}\,w$ whose Laurent series lies in `NodeLocalized.fieldOver (N * q) K` — is local. Assume the value integrality law `R.ValueIntegralityLaw w`: for every $f \in R.\mathrm{nodeIntegers}\,w$ and every place $V$ of `modularFunctionFieldBar (N * q)` over $\overline{\mathbb Q}$ with $P.\mathrm{reduceFst}\,V = w$, the value $V.\mathrm{evalAt}\,f$ lies in $A$. Then for such a $V$ and every $g \in B$, the $A$-valuation of $V.\mathrm{evalAt}\,g$ is $<1$ if and only if $g$ lies in the maximal ideal of $B$.
--
--   The statement identifies the centre on the node ring $B$ of the composite of the place $V$ with the valuation of $A$: the non-units of $B$ are exactly the elements whose value at any place over $w$ is non-integral at $A$. It is used in the comparison of the node ring with the crossing model $W[[X,Y]]/(XY - \cdot)$ and in counting arguments bounding the number of points by sums of residue-field degrees.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_valuation_evalAt_lt_one_iff_mem_maximalIdeal.lean

import Mathlib
import Definitions.Def_ModularCurve_NodeDepth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.valuation_evalAt_lt_one_iff_mem_maximalIdeal
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N))
    [IsLocalRing ↥(R.nodeIntegersOver K w)] (hVI : R.ValueIntegralityLaw w)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hV : P.reduceFst V = w) (g : ↥(R.nodeIntegersOver K w)) :
    A.valuation (V.evalAt ((g : ↥(modularFunctionFieldBar (N * q))))) < 1 ↔ g ∈ IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) := by sorry
