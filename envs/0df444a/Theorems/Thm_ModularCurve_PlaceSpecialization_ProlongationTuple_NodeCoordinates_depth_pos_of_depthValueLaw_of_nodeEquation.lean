-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_NodeCoordinates_depth_pos_of_depthValueLaw_of_nodeEquation
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.NodeCoordinates.depth_pos_of_depthValueLaw_of_nodeEquation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/ced5b65e-1b2b-5450-b228-ff18fa888207
-- title:
--   Positivity of depth at inertia-fixed places over a node
-- statement:
--   Fix a prime $q$ and a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$ (the predicate `LiesOverPrime`), a nonzero level $N$ with $q \nmid N$, a perfect algebraically closed field $k$ of characteristic $q$, a ring homomorphism $red : A \to k$, modular polynomial data for $q$ satisfying the Kronecker congruence, integrality of the two degeneracy maps $\bar\alpha$, $\bar\beta$ from level $N$ to level $Nq$, a place specialisation $P$ for these data and a prolongation tuple $R$ over $P$. Assume $R$ satisfies `IsModel` (the two divisor laws and the two cusp laws), `OrderLawFixed`, and, for a finite set $W$ of places of `modularFunctionFieldC k N` all of which are supersingular places (rational, affine, with $j$-value in the supersingular set), the laws `RegularityLaw W` and `NodeValueLaw W`. Let $K$ be a finite extension of $\mathbb{Q}$ inside $\overline{\mathbb{Q}}$, let $w \in W$ satisfy the value-integrality law `ValueIntegralityLaw w`, and let $\varpi, \varepsilon$ lie in $A \cap K$ with $\varepsilon$ a unit and $q = \varpi^{e_K}\varepsilon$. Let $c$ be a node-coordinate datum at $(K,w)$, that is a pair $x, y$ of elements of the node integers over $K$ with $x$ reducing to $0$ on the first branch and of order $1$ at the Frobenius translate of $w$ on the second, and $y$ symmetrically, and suppose the node equation $x y = \varpi^{E e_K} u$ holds with $u$ a unit of the node integers over $K$. Finally let $\mathrm{depth}$ be a natural-number-valued function on the places of `modularFunctionFieldBar (N * q)` satisfying the depth-value law for $c$ at $w$: for every such place $V$ with $P.\mathrm{reduceFst}\, V = w$ that is fixed by the arithmetic Galois action of the inertia subgroup of $A$ over $\mathbb{Q}$, one has $v_A(y(V)) = v_A(q)^{\mathrm{depth}(V)}$. Then for any such inertia-fixed $V$ above $w$, $0 < \mathrm{depth}(V)$.
--
--   This is the lower half of the depth bound attached to a supersingular node on the special fibre at $q$ of the curve of level $Nq$: the depth of an inertia-fixed place lying over the node is strictly positive, the companion upper bound being $\mathrm{depth}(V) < E$. It feeds the computation of the component group and of the depth pairing used in the analysis of the Hecke action on the special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_NodeCoordinates_depth_pos_of_depthValueLaw_of_nodeEquation.lean

import Mathlib
import Definitions.Def_ModularCurve_NodeDepth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.NodeCoordinates.depth_pos_of_depthValueLaw_of_nodeEquation
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime q) {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [PerfectField k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (hmodel : R.IsModel) (hord : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W) (hvalA : R.ValueIntegralityLaw w)
    (ϖ : ↥(NodeLocalized.coeffSubring A K)) (eK : ℕ) (ε : ↥(NodeLocalized.coeffSubring A K)) (hε : IsUnit ε)
    (hqϖ : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε)
    (c : R.NodeCoordinates K w) (E : ℕ) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ (E * eK) * u)
    (depth : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) → ℕ) (hdepth : c.DepthValueLaw depth)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hV : P.reduceFst V = w)
    (hfix : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V) :
    0 < depth V := by sorry
