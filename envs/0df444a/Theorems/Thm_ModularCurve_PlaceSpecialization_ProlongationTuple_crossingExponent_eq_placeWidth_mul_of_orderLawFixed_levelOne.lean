-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_crossingExponent_eq_placeWidth_mul_of_orderLawFixed_levelOne
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.crossingExponent_eq_placeWidth_mul_of_orderLawFixed_levelOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/f9e2443b-3aeb-5920-bf62-8136451bb648
-- title:
--   Crossing exponent equals place width times e_K
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a field $k$ of characteristic $q$ that is algebraically closed, and a ring homomorphism $\mathrm{red} : A \to k$. Let `data` be a modular polynomial datum for $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$), let `hKr` be the Kronecker congruence $\Phi \equiv (Y^q - X)(Y - X^q) \bmod q$, and let `hα`, `hβ` assert integrality of the two Hecke maps $\bar\alpha, \bar\beta$ at level $1$ and prime $q$. Let $P$ be a place specialisation of these data and $R$ a prolongation tuple over $P$, and assume $5 \le q$, that $R$ `IsModel` (the two divisor laws together with the cusp laws at $\infty$ and at $0$), that $W$ is a finite set of places of $\mathrm{modularFunctionFieldC}\, k\, 1$ each of which is supersingular (rational, affine in $j$, with $j$-value in $\mathrm{ssJSet}\, q\, k$), and that $R$ satisfies the regularity law, the node value law and the fixed-order law on $W$. Assume further that $\ker(\mathrm{red})$ is the maximal ideal of $A$, that $K \subseteq \overline{\mathbb{Q}}$ is a number field, and that $w \in W$. Let $xw \in A \cap K$ reduce to $w.\mathrm{evalAt}(\mathrm{jGeomGen}\, k\, 1)$, let $\varpi \in A \cap K$ be an element whose multiples are exactly the elements of $A \cap K$ with zero reduction, and let $q = \varpi^{e_K}\varepsilon$ with $\varepsilon$ a unit of $A \cap K$. Finally let $c$ be a pair of node coordinates at $w$ over $K$ (elements $x, y$ of the node ring over $K$ with $\mathrm{residue}_1(x) = 0$, $\mathrm{ord}_{\mathrm{Frob}\cdot w}(\mathrm{residue}_2(x)) = 1$, $\mathrm{residue}_2(y) = 0$, $\mathrm{ord}_w(\mathrm{residue}_1(y)) = 1$), and suppose $c.x \cdot c.y = (\varpi)^{E} u$ in that ring, where $\varpi$ is pushed in through the constant embedding and $u$ is a unit. Then $E = \mathrm{placeWidth}\, 1\, w \cdot e_K$, where $\mathrm{placeWidth}\, 1\, w$ is $\mathrm{jWidth}$ of the $j$-value of $w$ (that is $3$, $2$ or $1$ according as the value is $0$, $1728$ or neither) divided by the ramification index $\mathrm{placeRamificationJ}\, 1\, w$.
--
--   This identifies the crossing exponent of the two branches through a supersingular point of the model at level one: the node equation $xy = \varpi^{E}u$ has $E$ equal to the width of the point times the absolute ramification index $e_K$, in accordance with the Deligne–Rapoport description of the special fibre of $X_0(q)$ as two copies of the $j$-line crossing at the supersingular points with the expected crossing multiplicities. It is used to produce component charts and annuli attached at the supersingular places, and in the width computation for the resolved model package.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_crossingExponent_eq_placeWidth_mul_of_orderLawFixed_levelOne.lean

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_PlaceWidth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.crossingExponent_eq_placeWidth_mul_of_orderLawFixed_levelOne
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hq : 5 ≤ q)
    (hmodel : R.IsModel)
    (W : Finset (Place k (modularFunctionFieldC k 1))) (hW : ∀ w ∈ W, w ∈ ssPlaces q 1 k)
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W) (hord : R.OrderLawFixed)
    (hker : ∀ c : ↥A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal ↥A)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W)
    (xw : ↥(NodeLocalized.coeffSubring A K)) (hxw : NodeLocalized.redRestrict red K xw = w.evalAt (jGeomGen k 1))
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (eK : ℕ) (ε : ↥(NodeLocalized.coeffSubring A K)) (hε : IsUnit ε)
    (hqe : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε)
    (c : R.NodeCoordinates K w) (E : ℕ) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E * u) :
    E = placeWidth 1 w * eK := by sorry
