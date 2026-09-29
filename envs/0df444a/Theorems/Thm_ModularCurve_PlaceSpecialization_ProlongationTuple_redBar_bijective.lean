-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_redBar_bijective
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.redBar_bijective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/a5097027-6a09-545b-81cc-50d886be3032
-- title:
--   Bijectivity of the residual constant map ̄red
-- statement:
--   Let $q$ be a prime, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$, let $k$ be a field of characteristic $q$ and let $\mathrm{red} \colon A \to k$ be a ring homomorphism. Let `data` be modular polynomial data at level $q$, that is a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair of $q$-expansions, let `hKr` be the Kronecker congruence for it, namely that the reduction of $\Phi$ modulo $q$ equals $(C(X)^q - X)(C(X) - X^q)$, and let `hα`, `hβ` assert that the two Hecke maps $\overline{\alpha}$, $\overline{\beta}$ from the Laurent base change of the full modular function field of level $1$ to that of level $q$ are integral ring homomorphisms. Let $P$ be a place specialization of type `PlaceSpecialization A q 1 data hKr k red hα hβ` — a package consisting of a map $\mathrm{sp}$ on places, a homomorphism on degree-zero divisor classes, and compatibility clauses relating orders of vanishing of $j$ and its $N$-twist before and after reduction — and let $R$ be a prolongation tuple for $P$, whose first two components are a ring homomorphism $\overline{\mathrm{red}} \colon \kappa_A \to k$ from the residue field of $A$ together with the identity $\overline{\mathrm{red}}(\mathrm{residue}_A(a)) = \mathrm{red}(a)$ for all $a \in A$. Then $\overline{\mathrm{red}}$ is bijective.
--
--   The statement identifies the residue field $\kappa_A$ of the chosen valuation subring of $\overline{\mathbb{Q}}$ with the base field $k$ of the reduction, once a level-one place specialization together with a prolongation tuple exists; consequently constructions carried out over $(\kappa_A, \mathrm{residue}_A)$ transfer to $(k, \mathrm{red})$. It is used in the construction of component charts and attached annuli for models of the level-$q$ modular curve in characteristic $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_redBar_bijective.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization.ProlongationTuple
open ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.redBar_bijective
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : ProlongationTuple P) :
    Function.Bijective R.redBar := by sorry
