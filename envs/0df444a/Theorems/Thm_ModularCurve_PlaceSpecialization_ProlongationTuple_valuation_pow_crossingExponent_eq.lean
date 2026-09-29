-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_valuation_pow_crossingExponent_eq
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.valuation_pow_crossingExponent_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/770e99eb-d104-592e-bb74-b4e0730051a3
-- title:
--   Presentation-invariance of the node crossing valuation
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a level $N \neq 0$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$, together with modular polynomial data for $q$ satisfying the Kronecker congruence, the integrality hypotheses $h\alpha$, $h\beta$ for the two degeneracy maps at level $N\cdot q$, a place specialisation $P$ for these data and a prolongation tuple $R$ over $P$. Assume $q \nmid N$, that $R$ is a model (the two divisor laws together with the two cusp laws), and fix a finite set $W$ of places of $\mathrm{modularFunctionFieldC}\ k\ N$ all of which are supersingular (rational, affine, with $j$-value in $\mathrm{ssJSet}$), for which $R$ satisfies the regularity law and the node value law. Fix $w \in W$ for which $R$ satisfies the value integrality law, i.e. every $f$ in the node integers at $w$ has $V.\mathrm{evalAt}\ f \in A$ for each place $V$ of $\mathrm{modularFunctionFieldBar}\ (N q)$ with $P.\mathrm{reduceFst}\ V = w$. Given two presentations of the crossing at $w$: a finite extension $K/\mathbb{Q}$ inside $\overline{\mathbb{Q}}$, an element $\varpi$ of $A \cap K$, node coordinates $c$ over $K$ at $w$, an exponent $E$ and a unit $u$ of the node integers over $K$ with $c.x\, c.y = (\varpi)^E u$, where $\varpi$ is taken as a constant via $\mathrm{nodeConst}$; and likewise $K_0$, coordinates $c_1$, exponent $E_0$ and unit $u_0$ with $c_1.x\, c_1.y = (q)^{E_0} u_0$. The conclusion is the equality $v_A(\varpi)^E = v_A(q)^{E_0}$ in the value group of $A$.
--
--   This is the statement that the total valuation of the crossing parameter in a local equation $xy = \varpi^E \cdot (\text{unit})$ at a supersingular node of the special fibre at $q$ depends only on the node, not on the chosen uniformiser, exponent, unit, or coefficient field of the presentation. It is used to compare an arbitrary presentation with a $q$-adic one, and is cited in the computation of the crossing exponent in terms of the place width and ramification of $j$, and in the identification of the node depths attached to node coordinates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_valuation_pow_crossingExponent_eq.lean

import Definitions.Def_ModularCurve_NodeDepth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.valuation_pow_crossingExponent_eq
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
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
    (hvalA : R.ValueIntegralityLaw w)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (c : R.NodeCoordinates K w) (E : ℕ) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E * u)
    (K₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K₀]
    (c₁ : R.NodeCoordinates K₀ w) (E₀ : ℕ) (u₀ : ↥(R.nodeIntegersOver K₀ w)) (hu₀ : IsUnit u₀)
    (hxy₁ : c₁.x * c₁.y = R.nodeConst K₀ w ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)) ^ E₀ * u₀) :
    A.valuation (ϖ : AlgebraicClosure ℚ) ^ E = A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ E₀ := by sorry
