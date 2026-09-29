-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_crossingExponent_eq_placeWidth_mul_of_orderLawFixed_of_placeRamificationJ_eq_one
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.crossingExponent_eq_placeWidth_mul_of_orderLawFixed_of_placeRamificationJ_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/803d72ef-0aaf-5ed5-a058-f71bdd4fd6d9
-- title:
--   Crossing exponent at an unramified supersingular node equals jWidth· e_K
-- statement:
--   Fix a prime $q$ with $5 \le q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a natural number $N \ge 1$ with $q \nmid N$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$ whose kernel is exactly the maximal ideal of $A$ (hypothesis `hker`). Fix further a modular polynomial datum `data` for $q$ satisfying the Kronecker congruence `hKr`, integrality of the two Hecke degeneracy embeddings at level $N\cdot q$ (`hα`, `hβ`), a place specialization $P$ built from these, and a prolongation tuple $R$ over $P$. The tuple is assumed to satisfy `R.IsModel` (the two divisor laws at places not fixed by the square of the geometric Frobenius, together with the two cusp laws), and, relative to a finite set $W$ of places of `modularFunctionFieldC k N` all of which lie in `ssPlaces q N k` (rational, affine for $j$ and $j_N$, with $j$-value in `ssJSet q k`), the regularity law `hreg`, the node-value law `hval` and the order law `hord` for places fixed by the square of Frobenius. Let $K \subset \overline{\mathbb{Q}}$ be finite over $\mathbb{Q}$ and put $\mathcal{O} = A \cap K$ (`NodeLocalized.coeffSubring A K`), with reduction $\mathrm{red}$ restricted to $\mathcal{O}$. Let $w \in W$ be a place with $\mathrm{placeRamificationJ}\,N\,w = 1$, that is, $\mathrm{ord}_w\bigl(j - w.\mathrm{evalAt}(j)\bigr) = 1$, let $x_w \in \mathcal{O}$ reduce to $w.\mathrm{evalAt}(j)$, let $\varpi \in \mathcal{O}$ generate the kernel of the reduction on $\mathcal{O}$ (an element of $\mathcal{O}$ reduces to $0$ precisely when it is a multiple of $\varpi$), and let $q = \varpi^{e_K}\varepsilon$ with $\varepsilon$ a unit of $\mathcal{O}$. Then for every node-coordinate datum $c = (x,y)$ over $K$ at $w$ — a pair of elements of $R.\mathrm{nodeIntegersOver}\,K\,w$ with first residue of $x$ zero, second residue of $x$ of order $1$ at the Frobenius-translated place, second residue of $y$ zero and first residue of $y$ of order $1$ at $w$ — every natural number $E$, and every unit $u$ of $R.\mathrm{nodeIntegersOver}\,K\,w$ with $x\,y = (\varpi\cdot 1)^E u$, where $\varpi$ is viewed in the node ring through `R.nodeConst K w`, one has $E = \mathrm{placeWidth}\,N\,w \cdot e_K$; under the hypothesis $\mathrm{placeRamificationJ}\,N\,w = 1$ the factor $\mathrm{placeWidth}\,N\,w$ is $\mathrm{jWidth}$ of the $j$-value of $w$, namely $3$ at $j = 0$, $2$ at $j = 1728$ and $1$ otherwise.
--
--   This is the computation of the thickness of the node of the reduction of $X_0(Nq)$ at a supersingular place $w$ that is unramified over the $j$-line: the crossing exponent of any node equation there is the level-one thickness $\mathrm{jWidth}(j(w))$ times the absolute ramification index $e_K$ of the coefficient ring $A \cap K$. It is the unramified case feeding the general statement `crossingExponent_eq_placeWidth_mul_of_orderLawFixed`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_crossingExponent_eq_placeWidth_mul_of_orderLawFixed_of_placeRamificationJ_eq_one.lean

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_PlaceWidth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization
open ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.crossingExponent_eq_placeWidth_mul_of_orderLawFixed_of_placeRamificationJ_eq_one
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N) (hq : 5 ≤ q)
    (hmodel : R.IsModel)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W) (hord : R.OrderLawFixed)
    (hker : ∀ c : ↥A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal ↥A)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
    (hr : placeRamificationJ N w = 1)
    (xw : ↥(NodeLocalized.coeffSubring A K)) (hxw : NodeLocalized.redRestrict red K xw = w.evalAt (jGeomGen k N))
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (eK : ℕ) (ε : ↥(NodeLocalized.coeffSubring A K)) (hε : IsUnit ε)
    (hqe : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε)
    (c : R.NodeCoordinates K w) (E : ℕ) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E * u) :
    E = placeWidth N w * eK := by sorry
