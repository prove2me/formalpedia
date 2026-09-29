-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_depthDual_eq_zero_of_isGoodDiv
-- name    : ModularCurve.PlaceSpecialization.depthDual_eq_zero_of_isGoodDiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/1ac1233e-0299-5fbc-8fdd-24289103e187
-- title:
--   Vanishing of the depth functional on good divisors
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a positive integer $N$, a field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$. Let `data` be modular polynomial data for $q$ (a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the $q$-th modular relation for the $j$-expansions), let `hKr` witness the Kronecker congruence $\Phi \equiv (Y^{q}-X)(Y-X^{q}) \bmod q$ in the form `reduceModBivar`, and let `hα`, `hβ` witness that the ring homomorphisms underlying `heckeAlphaBar` and `heckeBetaBar` for level $N$ and $q$ over $\overline{\mathbb Q}$ are integral. Let $P$ be a place specialization of these data, $g$ an element of `SemilinearAut k (modularFunctionFieldC k N)` (a pair consisting of a ring automorphism of the level-$N$ function field and one of $k$, compatible with the structure map), and $W$ a finite set of places of `modularFunctionFieldC k N` over $k$ each of which is fixed by the square of `frobOnPlacesGeomLevel k N data hKr`. Let `depth` be an arbitrary $\mathbb N$-valued function on the places of `modularFunctionFieldBar (N * q)` over $\overline{\mathbb Q}$, and let $D$ be a divisor there, i.e. a finitely supported $\mathbb Z$-valued function on those places, which is good in the sense that every place in the support of $D$ satisfies `P.IsStrictFst` or `P.IsStrictSnd`. Then the functional `P.depthDual g W depth D`, namely the sum over the node pairs of $W$ of `P.depthDiv depth D` evaluated at the first coordinate of the pair times the corresponding crossing coordinate, is zero in the $\mathbb Z$-dual of the character lattice of those node pairs.
--
--   This is the vanishing clause of the component-specialization law for the Néron model of $J_0(Nq)$ at $q$: a divisor all of whose points reduce strictly to one of the two copies of $X_0(N)$ contributes nothing along the exceptional chains over the supersingular crossings. It is used in the comparison of the depth functional with the Hecke action on the component group of the special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_depthDual_eq_zero_of_isGoodDiv.lean

import Mathlib
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_GlueData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.depthDual_eq_zero_of_isGoodDiv
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (g : SemilinearAut k (modularFunctionFieldC k N))
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (hW : ∀ w ∈ W, frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) = w)
    (depth : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) → ℕ)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hgood : P.IsGoodDiv D) :
    P.depthDual g W depth D = 0 := by sorry
