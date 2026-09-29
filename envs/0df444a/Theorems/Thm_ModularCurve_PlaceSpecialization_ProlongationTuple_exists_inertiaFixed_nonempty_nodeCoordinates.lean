-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_inertiaFixed_nonempty_nodeCoordinates
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_inertiaFixed_nonempty_nodeCoordinates
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/8da05624-3eb7-5a05-8b49-3bcee3f5d058
-- title:
--   Node coordinates at a supersingular place over an inertia-fixed field
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a positive level $N$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$; fix further a modular polynomial datum $\mathrm{data}$ for $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j(q), j(q^{q}))$), a proof $hKr$ that its bivariate reduction mod $q$ equals $(X^{q}-Y)(X-Y^{q})$, and proofs $h\alpha$, $h\beta$ that the two Hecke maps $\overline{\alpha}$, $\overline{\beta}$ at level $N$ and prime $q$ over $\overline{\mathbb{Q}}$ are integral ring homomorphisms. Let $P$ be a place specialisation of these data and $R$ a prolongation tuple over $P$. Assume $q \nmid N$, that $R$ satisfies `IsModel` (the conjunction of its two divisor laws and its two cusp laws at $\infty$ and at $0$), that $W$ is a finite set of places of the function field $modularFunctionFieldC\ k\ N = k(j(q), j(q^{N}))$ all of which satisfy the supersingularity predicate `IsSupersingularPlace` for $q$, $N$ over $k$, that $R$ satisfies the regularity law and the node-value law for $W$, and let $w \in W$. Then there is an intermediate field $K$ of $\mathbb{Q} \subseteq \overline{\mathbb{Q}}$, finite-dimensional over $\mathbb{Q}$, fixed pointwise by every element of the inertia subgroup of $A$ inside $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$, such that the type of node coordinates $R.NodeCoordinates\ K\ w$ is nonempty: there exist $x, y$ in the ring of node integers of $R$ over $K$ at $w$ with $x$ killed by the first residue map at $w$ and of order $1$ at the place $\varphi \cdot w$ for the arithmetic Frobenius translate under the second residue map, and $y$ killed by the second residue map while having order $1$ at $w$ under the first.
--
--   This supplies, at a supersingular place $w$ of the geometric special fibre, a pair of local coordinates cutting out the two crossing branches of the model of $X_0(Nq)$, with coefficients in a finite extension of $\mathbb{Q}$ on which the inertia group at $A$ acts trivially. It feeds the companion statement [`ModularCurve.PlaceSpecialization.ProlongationTuple.exists_inertiaFixed_field_nonempty_nodeCoordinates`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.exists_inertiaFixed_field_nonempty_nodeCoordinates), and through it the analysis of the nodes used in the Kronecker-congruence description of the reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_inertiaFixed_nonempty_nodeCoordinates.lean

import Definitions.Def_ModularCurve_NodeLocalizedPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_inertiaFixed_nonempty_nodeCoordinates
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (hmodel : R.IsModel)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W)
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W) :
    ∃ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K),
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ z ∈ K, σ z = z) ∧ Nonempty (R.NodeCoordinates K w) := by sorry
