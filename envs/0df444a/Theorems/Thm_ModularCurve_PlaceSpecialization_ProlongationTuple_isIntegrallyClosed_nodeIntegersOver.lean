-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isIntegrallyClosed_nodeIntegersOver
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.isIntegrallyClosed_nodeIntegersOver
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/32c1911a-25ca-513c-993e-32e952a6edcb
-- title:
--   The K-rational node ring is integrally closed
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a positive integer $N$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$. Let $data$ be a `ModularPolynomialData` for $q$, that is a monic polynomial $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ in $Y$ annihilating the pair $(j, j_q)$ of $q$-expansions, and let $hKr$ be the Kronecker congruence for it, namely that the reduction of $\Phi$ modulo $q$ equals $(C(X)^q - X)\,(C(X) - X^q)$. Let $h\alpha$, $h\beta$ assert that the two degeneracy inclusions $\overline{\alpha}$, $\overline{\beta}$ from level $N$ to level $N\ell$ over $\overline{\mathbb Q}$ are integral ring homomorphisms, let $P$ be a place specialisation of these data and $R$ a prolongation tuple over $P$. Finally let $K$ be an intermediate field of $\mathbb Q \subseteq \overline{\mathbb Q}$ and $w$ a place of the fibre function field `modularFunctionFieldC k N` over $k$. The assertion is that the subring $R.\mathrm{nodeIntegersOver}\,K\,w$ of `modularFunctionFieldBar (N * q)`, consisting of those $f$ lying in the subring `R.nodeIntegers w` whose $q$-expansion lies in `NodeLocalized.fieldOver (N * q) K`, is integrally closed, i.e. every element of its fraction field integral over it comes from the ring.
--
--   This is the normality statement for the ring of functions on $X_0(Nq)$ regular at a node over the place $w$ and with $q$-expansion coefficients constrained to $K$; it is used as a standing hypothesis for the local algebra at the nodes, feeding the length and degree computations such as [`ModularCurve.PlaceSpecialization.ProlongationTuple.length_localizedModule_quotient_map_eq_of_mem_minimalPrimes`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.length_localizedModule_quotient_map_eq_of_mem_minimalPrimes) and [`ModularCurve.PlaceSpecialization.ProlongationTuple.card_eq_finsum_finrank_quotient_of_forall_iff_evalAt_eq_zero`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.card_eq_finsum_finrank_quotient_of_forall_iff_evalAt_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isIntegrallyClosed_nodeIntegersOver.lean

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_AlgebraicCurve_GluedPic0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.isIntegrallyClosed_nodeIntegersOver
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (w : Place k (modularFunctionFieldC k N)) :
    IsIntegrallyClosed ↥(R.nodeIntegersOver K w) := by sorry
