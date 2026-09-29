-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces
-- name    : ModularCurve.PlaceSpecialization.frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/3b0404ec-8cb8-54ab-b7e9-c9c14fe936d6
-- title:
--   Frobenius squared fixes supersingular places under a place specialization
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a nonzero natural number $N$, a field $k$ of characteristic $q$ with decidable equality, a ring homomorphism $\mathrm{red} : A \to k$, and data $\mathrm{data} : \mathtt{ModularPolynomialData}\ q$, that is a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j(q\cdot), j)$ of $q$-expansions. Assume $\mathrm{hKr}$, the Kronecker congruence that the reduction of $\Phi$ modulo $q$ equals $(C(X)^q - X)(C(X) - X^q)$, and the hypotheses $h\alpha$, $h\beta$ that the two Hecke maps $\overline{\alpha}$, $\overline{\beta}$ at level $N$ and prime $q$ over $\overline{\mathbb{Q}}$ are integral ring homomorphisms. Assume further $q \nmid N$, and let $P$ be a place specialization $\mathtt{PlaceSpecialization}\ A\ q\ N\ \mathrm{data}\ \mathrm{hKr}\ k\ \mathrm{red}\ h\alpha\ h\beta$, i.e. a map $\mathrm{sp}$ from places of the level-$N$ modular function field over $\overline{\mathbb{Q}}$ to places of $\mathtt{modularFunctionFieldC}\ k\ N = k(j, j_N)$ inside $k$-Laurent series, together with an additive map on the degree-zero Picard group and compatibility clauses relating the orders of $j - a$ and $j_N - a$ at $w$ to those of $j - \mathrm{red}(a)$ and $j_N - \mathrm{red}(a)$ at $\mathrm{sp}(w)$. Then for every place $w$ of $k(j,j_N)$ over $k$ (a proper valuation subring containing $k$ whose ring is a principal ideal ring) lying in $\mathtt{ssPlaces}\ q\ N\ k$, i.e. satisfying $\mathtt{IsSupersingularPlace}\ q\ N\ k\ w$, the geometric Frobenius operation $\mathtt{frobOnPlacesGeomLevel}$ — restriction of $w$ to the image of $k(j,j_N)$ under the $q$-power $q$-expansion embedding, transported back along the induced isomorphism — satisfies $\mathrm{Frob}(\mathrm{Frob}(w)) = w$.
--
--   This records the involutivity of the geometric Frobenius correspondence on the supersingular locus of the level-$N$ modular curve in characteristic $q \nmid N$, the place-theoretic counterpart of the fact that Frobenius composed with itself acts trivially there. It is the form of the statement usable inside the place-specialization framework, and is invoked by the analysis of prolongation tuples and local models at supersingular crossings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces.lean

import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_SupersingularNodePlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
open AlgebraicCurve

theorem ModularCurve.PlaceSpecialization.frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k] [DecidableEq k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k) :
    frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) = w := by sorry
