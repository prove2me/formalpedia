-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_inertiaFixed_nonempty_nodeCoordinates_levelOne
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_inertiaFixed_nonempty_nodeCoordinates_levelOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/7bb18ab7-e645-5d97-8299-3b592b015e82
-- title:
--   Inertia-fixed node coordinates at a supersingular place, level one
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$. Let `data` be a `ModularPolynomialData` for $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j(q), j(q^{\,\cdot}))$), let `hKr` be the Kronecker congruence asserting that the bivariate reduction of $\Phi$ modulo $q$ factors as $(C X^q - X)(C X - X^q)$, and let `hα`, `hβ` be the integrality of the two Hecke correspondence homomorphisms at level $1$ and prime $q$. Let $P$ be a `PlaceSpecialization` of this data and $R$ a `ProlongationTuple` over $P$. Assume $q \nmid 1$, that $R$ satisfies `IsModel` (the two divisor laws together with the two cusp laws at $\infty$ and at $0$), that $W$ is a finite set of places of `modularFunctionFieldC k 1` all lying in `ssPlaces q 1 k`, that $R$ satisfies the regularity law and the node value law on $W$, and let $w \in W$. Then there is an intermediate field $K$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, finite over $\mathbb{Q}$, fixed pointwise by every element of the inertia subgroup `A.inertiaSubgroupIn ℚ` (the image of the inertia subgroup of $A$ in $\overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$), such that `R.NodeCoordinates K w` is nonempty: there are $x, y$ in the node integers over $K$ at $w$ with the first residue of $x$ zero and the second residue of $x$ of order $1$ at the Frobenius translate `arithFrobC q k 1 • w`, and symmetrically the second residue of $y$ zero and the first residue of $y$ of order $1$ at $w$.
--
--   At level one this provides the local coordinates transverse to the two branches of the reduction of $X_0(q)$ at a supersingular point, with coefficients in a field finite over $\mathbb{Q}$ on which inertia at the chosen place acts trivially. It is used in the construction of a prolongation tuple carrying node coordinates and satisfying the depth value law at level one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_inertiaFixed_nonempty_nodeCoordinates_levelOne.lean

import Definitions.Def_ModularCurve_NodeLocalizedPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_inertiaFixed_nonempty_nodeCoordinates_levelOne
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ 1)
    (hmodel : R.IsModel)
    (W : Finset (Place k (modularFunctionFieldC k 1))) (hW : ∀ w ∈ W, w ∈ ssPlaces q 1 k)
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W)
    (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W) :
    ∃ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K),
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ z ∈ K, σ z = z) ∧ Nonempty (R.NodeCoordinates K w) := by sorry
