-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_NodeCoordinates_depth_lt_of_depthValueLaw_of_nodeEquation
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.NodeCoordinates.depth_lt_of_depthValueLaw_of_nodeEquation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/60b0eb4d-ddf5-5507-83d3-38db9db6027e
-- title:
--   Depth of an inertia-fixed place over a node is less than E
-- statement:
--   Fix a prime $q$ and a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q\in A$ a non-unit (`A.LiesOverPrime q`), a non-zero level $N$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$, together with modular polynomial data `data` for $q$ satisfying the Kronecker congruence `hKr`, integrality of the two Hecke maps $\bar\alpha,\bar\beta$ from level $N$ to level $Nq$, and a place specialization $P$ built from these. Let $R$ be a prolongation tuple over $P$, assume $q \nmid N$, that $R$ is a model (the two divisor laws and the two cusp laws), and that $R$ satisfies the order law at Frobenius-fixed affine geometric places. Let $W$ be a finite set of places of the level-$N$ geometric function field over $k$, each supersingular (rational, affine, with $j$-value in the supersingular set), and assume the regularity law and the node-value law for $R$ over $W$. Let $K$ be a finite extension of $\mathbb{Q}$ inside $\overline{\mathbb{Q}}$, let $w \in W$, and assume the value-integrality law at $w$: every element of `R.nodeIntegers w` has value in $A$ at every place $V$ of the level-$Nq$ field over $\overline{\mathbb{Q}}$ with `P.reduceFst V = w`. Let $\varpi, \varepsilon$ lie in $A \cap K$ with $\varepsilon$ a unit of that ring and $q = \varpi^{e_K}\varepsilon$, and let $c$ be a node-coordinate datum at $w$ over $K$, i.e. elements $x, y$ of `R.nodeIntegersOver K w` with $x$ reducing to $0$ under the first residue map, $y$ reducing to $0$ under the second, $\operatorname{ord}_w$ of the first residue of $y$ equal to $1$, and $\operatorname{ord}$ at the Frobenius translate of $w$ of the second residue of $x$ equal to $1$. Suppose $xy = (\text{nodeConst}_K^w \varpi)^{E e_K} u$ for a unit $u$ of `R.nodeIntegersOver K w`, and let $\mathrm{depth}$ be a function on places of the level-$Nq$ field satisfying the depth-value law for $c$: for every $V$ with `P.reduceFst V = w` that is fixed by the arithmetic Galois action of the inertia subgroup of $A$ over $\mathbb{Q}$, the $A$-valuation of the value of $y$ at $V$ equals $v_A(q)^{\mathrm{depth}\,V}$. Then for any such inertia-fixed $V$ above $w$ one has $\mathrm{depth}\,V < E$.
--
--   This is the quantitative bound on the depth of a place of the level-$Nq$ modular function field lying over a supersingular node of the special fibre: the depth recorded by the depth-value law is strictly smaller than the width $E$ appearing in the node equation $xy = \varpi^{E e_K} u$. It feeds the depth hypotheses of the component-group and Deligne–Rapoport model computations that use the node dictionary at supersingular points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_NodeCoordinates_depth_lt_of_depthValueLaw_of_nodeEquation.lean

import Mathlib
import Definitions.Def_ModularCurve_NodeDepth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing
open ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.NodeCoordinates.depth_lt_of_depthValueLaw_of_nodeEquation
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
    depth V < E := by sorry
