-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_NodeCoordinates_depth_lt_mul_of_yDepth_pow_eq
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.NodeCoordinates.depth_lt_mul_of_yDepth_pow_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/8f100ee8-aa75-5757-8095-2d19babf533e
-- title:
--   Depth bound at a supersingular node: depth V < e'E
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$ with $q$ a non-unit of $A$, a positive integer $N$ with $q \nmid N$, and a perfect, algebraically closed field $k$ of characteristic $q$ together with a ring homomorphism $red : A \to k$. Let `data` be modular polynomial data at level $q$ satisfying the Kronecker congruence $\Phi \equiv (Y^q - X)(Y - X^q) \bmod q$, let $h\alpha, h\beta$ be the integrality hypotheses for the two degeneracy maps from level $N$ to level $Nq$, let $P$ be a place specialisation for these data and $R$ a prolongation tuple over $P$. Assume $R$ is a model (the two divisor laws and the two cusp laws), satisfies the fixed-place order law, and, for a finite set $W$ of places of the geometric level-$N$ function field over $k$ all of which are supersingular (rational, affine, with supersingular $j$-value), satisfies the regularity law and the node value law for $W$. Let $K \subset \overline{\mathbb Q}$ be a finite extension of $\mathbb Q$, let $w \in W$, and assume the value integrality law of $R$ at $w$. In the subring $A \cap K$ of $\overline{\mathbb Q}$ let $\varpi$ and a unit $\varepsilon$ satisfy $q = \varpi^{e_K}\varepsilon$. Let $c$ be a pair of node coordinates $x, y$ at $w$ over $K$, that is, elements of the ring of functions on the level-$Nq$ curve that are integral for both prolongations, integral at every place above $w$ and defined over $K$, with $x$ reducing to $0$ on the first branch and to a uniformiser at the Frobenius-twisted place on the second, and $y$ reducing to $0$ on the second branch and to a uniformiser at $w$ on the first. Suppose $x y = (\varpi)^{E e_K} u$ with $u$ a unit of that ring, $(\varpi)$ denoting the image of $\varpi$ as a constant function. Finally let $e' \ge 1$, let `depth` be any function from places of the level-$Nq$ function field over $\overline{\mathbb Q}$ to $\mathbb N$, and let $V$ be such a place with $P.\mathrm{reduceFst}\,V = w$ and with the $y$-depth of $V$, namely the $A$-valuation of the value of $y$ at $V$, satisfying $(\text{yDepth}\,V)^{e'} = v_A(q)^{\text{depth}\,V}$ in the value group of $A$. Then $\text{depth}\,V < e' E$.
--
--   This is the strict bound on the normalised depth of a place of the level-$Nq$ function field lying over a supersingular node of the characteristic-$q$ fibre: the depth, measured on the scale $1/e'$ so that ramified places above the node are admitted, stays strictly below the crossing exponent $E$ of the node equation $xy = \varpi^{Ee_K}u$. It is used in the computation of the component-group pairing, being cited by [`ModularCurve.PlaceSpecialization.depthDual_add_mem_range_gramMap_of_isPrincipal`](thm.html#ModularCurve.PlaceSpecialization.depthDual_add_mem_range_gramMap_of_isPrincipal) and by [`ModularCurve.PlaceSpecialization.depthDual_add_mem_range_gramMap_of_isPrincipal_widthChar`](thm.html#ModularCurve.PlaceSpecialization.depthDual_add_mem_range_gramMap_of_isPrincipal_widthChar).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_NodeCoordinates_depth_lt_mul_of_yDepth_pow_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_NodeDepth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.NodeCoordinates.depth_lt_mul_of_yDepth_pow_eq
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
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ (E * eK) * u) (e' : ℕ) (he' : 1 ≤ e')
    (depth : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) → ℕ)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hV : P.reduceFst V = w)
    (hdepth : c.yDepth V ^ e' = A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ^ depth V) :
    depth V < e' * E := by sorry
