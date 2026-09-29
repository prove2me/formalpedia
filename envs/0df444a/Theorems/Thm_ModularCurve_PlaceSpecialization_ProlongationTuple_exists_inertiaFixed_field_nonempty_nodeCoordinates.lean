-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_inertiaFixed_field_nonempty_nodeCoordinates
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_inertiaFixed_field_nonempty_nodeCoordinates
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/956a5a5e-acd1-5000-b812-d276d2ba4798
-- title:
--   Node coordinates over an inertia-fixed field with uniformiser q
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$ (the chosen algebraic closure of $\mathbb{Q}$), a positive level $N$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$; fix modular polynomial data `data` for $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair of $q$-expansions) together with a proof `hKr` that its reduction modulo $q$ equals $(\,\mathrm{C}\,X^{q} - X)(\mathrm{C}\,X - X^{q})$, and proofs `hα`, `hβ` that the two Hecke ring homomorphisms at level $N$ and prime $q$ over $\overline{\mathbb{Q}}$ are integral. Let $P$ be a place specialization of these data and $R$ a prolongation tuple over $P$. Assume $q \nmid N$, that $R$ satisfies `IsModel` (the two divisor laws and the cusp laws at $\infty$ and at $0$), and let $W$ be a finite set of places of the level-$N$ function field $\mathrm{modularFunctionFieldC}\,k\,N$ all of which are supersingular for $q$, for which $R$ satisfies the regularity law and the node-value law on $W$; let $w \in W$. Then there is an intermediate field $K$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, finite over $\mathbb{Q}$, such that: every element of the inertia subgroup of $A$ over $\mathbb{Q}$ (the image of `A.inertiaSubgroup ℚ` in $\mathrm{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$) fixes each element of $K$; an element $d$ of the coefficient ring $A \cap K$ has $\mathrm{red}(d) = 0$ exactly when $d \in q\,(A \cap K)$, so $q$ generates the kernel of the reduction there; and the type `R.NodeCoordinates K w` is non-empty, i.e. there are $x, y$ in $R$'s node integers over $K$ at $w$ with $\mathrm{residue}_1(x) = 0$, $\mathrm{ord}_{\varphi \cdot w}(\mathrm{residue}_2(x)) = 1$ for $\varphi$ the arithmetic Frobenius translation, $\mathrm{residue}_2(y) = 0$ and $\mathrm{ord}_w(\mathrm{residue}_1(y)) = 1$.
--
--   This is the existence of a node-coordinate datum at a supersingular node of the two-component special fibre at $q$, with coefficients in a finite extension of $\mathbb{Q}$ on which inertia at $A$ acts trivially and in whose ring of coefficients $q$ itself is a uniformiser; it sharpens `exists_inertiaFixed_nonempty_nodeCoordinates` by the uniformiser clause, obtained from [`FinFlatHopf.inertiaFixed_valuationSubring_dvr_fixer_le_inertia`](thm.html#FinFlatHopf.inertiaFixed_valuationSubring_dvr_fixer_le_inertia). It feeds the statements producing presentations of node coordinates and the depth computations attached to the order law.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_inertiaFixed_field_nonempty_nodeCoordinates.lean

import Definitions.Def_ModularCurve_NodeLocalizedPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_inertiaFixed_field_nonempty_nodeCoordinates
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
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ z ∈ K, σ z = z) ∧
      (∀ d : ↥(NodeLocalized.coeffSubring A K),
          NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) * d') ∧
      Nonempty (R.NodeCoordinates K w) := by sorry
