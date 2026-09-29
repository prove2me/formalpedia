-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_crossingExponent_eq_placeWidth_mul_of_orderLawFixed_of_one_lt_placeRamificationJ
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.crossingExponent_eq_placeWidth_mul_of_orderLawFixed_of_one_lt_placeRamificationJ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/18710afa-995d-5505-8908-bf57a3adeb8f
-- title:
--   Crossing exponent at a ramified supersingular node
-- statement:
--   Let $q \ge 5$ be a prime with $q \nmid N$, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$, let $k$ be an algebraically closed field of characteristic $q$ and $\mathrm{red} : A \to k$ a ring homomorphism whose kernel is exactly the maximal ideal of $A$, let `data` be modular polynomial data for $q$ satisfying the Kronecker congruence `hKr`, and assume the two Hecke integrality hypotheses $h\alpha$, $h\beta$. Fix a place specialization $P$ for these data and a prolongation tuple $R$ over $P$ which is a model (the two divisor laws and the two cusp laws) and satisfies the fixed-place order law, together with the regularity law and the node-value law for a finite set $W$ of places of `modularFunctionFieldC k N`, each of which is supersingular (rational, affine geometric, with $j$-value in the supersingular set for $q$). Let $K \subseteq \overline{\mathbb{Q}}$ be a finite extension of $\mathbb{Q}$ and write $\mathcal{O} = A \cap K$ for the coefficient subring, with reduction `redRestrict red K` to $k$. Let $w \in W$ be ramified over the $j$-line, in the sense that $\operatorname{ord}_w\bigl(j - w(j)\bigr) > 1$ for the generator `jGeomGen k N`. Let $x_w \in \mathcal{O}$ reduce to $w$'s value $w(j)$, let $\varpi \in \mathcal{O}$ be such that an element of $\mathcal{O}$ reduces to $0$ precisely when it is a multiple of $\varpi$, and let $q = \varpi^{e_K}\varepsilon$ with $\varepsilon$ a unit. Finally let $c$ be a system of node coordinates for $R$ over $K$ at $w$ (elements $x, y$ of the ring of node integers over $K$ at $w$ with first residue of $x$ zero, second residue of $x$ of order $1$ at the Frobenius translate of $w$, second residue of $y$ zero, and first residue of $y$ of order $1$ at $w$), and suppose $x\,y = (\varpi)^{E} u$ in that ring, where $\varpi$ is carried over by `nodeConst` and $u$ is a unit. Then $E = \mathrm{placeWidth}\,N\,w \cdot e_K$, where $\mathrm{placeWidth}\,N\,w$ is the quotient of $\mathrm{jWidth}(w(j))$ (equal to $3$, $2$ or $1$ according as $w(j)$ is $0$, $1728$, or neither) by the ramification index $\operatorname{ord}_w(j - w(j))$.
--
--   This computes the thickness (crossing exponent) of the crossing of the two branches at a supersingular node of the reduction at $q$ of the modular curve of level $Nq$, in the case of a point ramified over the $j$-line, i.e. with $j$-invariant $0$ or $1728$; the unramified case is treated separately. It is used by [`ModularCurve.PlaceSpecialization.ProlongationTuple.crossingExponent_eq_placeWidth_mul_of_orderLawFixed`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.crossingExponent_eq_placeWidth_mul_of_orderLawFixed), which merges the two cases into a single formula for the width at an arbitrary supersingular place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_crossingExponent_eq_placeWidth_mul_of_orderLawFixed_of_one_lt_placeRamificationJ.lean

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_PlaceWidth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.crossingExponent_eq_placeWidth_mul_of_orderLawFixed_of_one_lt_placeRamificationJ
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
    (hr : 1 < placeRamificationJ N w)
    (xw : ↥(NodeLocalized.coeffSubring A K)) (hxw : NodeLocalized.redRestrict red K xw = w.evalAt (jGeomGen k N))
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (eK : ℕ) (ε : ↥(NodeLocalized.coeffSubring A K)) (hε : IsUnit ε)
    (hqe : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε)
    (c : R.NodeCoordinates K w) (E : ℕ) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E * u) :
    E = placeWidth N w * eK := by sorry
