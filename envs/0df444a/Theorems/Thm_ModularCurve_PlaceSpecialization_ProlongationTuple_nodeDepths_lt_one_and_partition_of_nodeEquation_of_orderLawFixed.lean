-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_nodeDepths_lt_one_and_partition_of_nodeEquation_of_orderLawFixed
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.nodeDepths_lt_one_and_partition_of_nodeEquation_of_orderLawFixed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/2677d5dc-dd95-5b57-be38-ec5c50233987
-- title:
--   Node depths below one partition the crossing exponent
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a nonzero level $N$, a field $k$ of characteristic $q$ that is algebraically closed, and a ring homomorphism $red : A \to k$; fix modular polynomial data `data` for $q$ satisfying the Kronecker congruence $\Phi \equiv (X_1^q - X_2)(X_1 - X_2^q) \bmod q$, integrality hypotheses $h\alpha, h\beta$ for the two degeneracy maps $\bar\alpha, \bar\beta$ from level $N$ to level $Nq$ over $\overline{\mathbb{Q}}$, a place specialization $P$ for these data, and a prolongation tuple $R$ over $P$. Assume $q \nmid N$, that $R$ satisfies `IsModel` (the two divisor laws together with the two cusp laws at the zero and infinity sides) and `OrderLawFixed` (the order formula at $\varphi^2$-fixed affine geometric places), and let $W$ be a finite set of places of `modularFunctionFieldC k N` each of which is supersingular, i.e. rational, affine geometric, and with $j$-value in `ssJSet q k`; assume the regularity law and the node value law for $W$. Let $K$ be a finite extension of $\mathbb{Q}$ inside $\overline{\mathbb{Q}}$, let $w \in W$, and assume the value integrality law at $w$: for every $f$ in the node ring at $w$ and every place $V$ of the level-$Nq$ function field over $\overline{\mathbb{Q}}$ with $P.\mathrm{reduceFst}\,V = w$, one has $V.\mathrm{evalAt}\,f \in A$. Let $\varpi \in A \cap K$, let $c$ be a node coordinate datum at $(K,w)$, consisting of $x, y$ in the node ring over $K$ at $w$ with first residue of $x$ zero, second residue of $x$ of order $1$ at $\mathrm{arithFrob} \cdot w$, second residue of $y$ zero, and first residue of $y$ of order $1$ at $w$; let $E \in \mathbb{N}$ and let $u$ be a unit of that node ring with $x y = (\varpi \cdot 1)^E u$, the constant $\varpi$ being taken into the node ring via `nodeConst`. Then for every place $V$ as above with $P.\mathrm{reduceFst}\,V = w$, writing $x$-depth and $y$-depth for $A$-valuations of the values $V.\mathrm{evalAt}\,x$ and $V.\mathrm{evalAt}\,y$, both depths are $< 1$ and their product equals $v_A(\varpi)^E$.
--
--   This is the quantitative statement that a characteristic-zero place of $X_0(Nq)$ lying over a supersingular node of the special fibre sits strictly inside the annulus over the crossing, at a position splitting the crossing exponent $E$ of the given local presentation $xy = \varpi^E u$ of the node ring. It feeds the construction of component charts and annuli at the nodes, and the computation of crossing exponents in terms of place widths.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_nodeDepths_lt_one_and_partition_of_nodeEquation_of_orderLawFixed.lean

import Definitions.Def_ModularCurve_NodeDepth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.nodeDepths_lt_one_and_partition_of_nodeEquation_of_orderLawFixed
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (hmodel : R.IsModel) (hord : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
    (hvalA : R.ValueIntegralityLaw w)
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (c : R.NodeCoordinates K w) (E : ℕ) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E * u)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hV : P.reduceFst V = w) :
    c.xDepth V < 1 ∧ c.yDepth V < 1 ∧
      c.xDepth V * c.yDepth V = A.valuation (ϖ : AlgebraicClosure ℚ) ^ E := by sorry
