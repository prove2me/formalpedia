-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_not_isUnit_sub_nodeConst_of_evalAt_mem_range_redRestrict_of_orderLawFixed
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_not_isUnit_sub_nodeConst_of_evalAt_mem_range_redRestrict_of_orderLawFixed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/0706f4ab-76fe-50cb-9a07-733969595a92
-- title:
--   Residue surjectivity of the node ring over K at a supersingular place
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a level $N\ge 1$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red}\colon A\to k$; fix modular polynomial data for $q$ (a monic $\Phi\in\mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair of $q$-expansions) satisfying the Kronecker congruence $\Phi \equiv (X^{q}-Y)(X-Y^{q})$ mod $q$, hypotheses asserting that the bar-Hecke homomorphisms $\bar\alpha,\bar\beta$ at level $N$ and prime $q$ over $\overline{\mathbb{Q}}$ are integral, a place specialization $P$ of these data, and a prolongation tuple $R$ over $P$. Assume $k$ algebraically closed, $q\nmid N$, that $R$ satisfies `OrderLawFixed` (at every affine place of the level-$N$ curve fixed by the square of the geometric Frobenius, the pushforward along `P.reduceFst` of the order divisor of any $f$ integral for both regular prolongations with nonzero residues equals $\mathrm{ord}$ of its first residue plus $\mathrm{ord}$ at the Frobenius translate of its second residue), and that $R$ satisfies `RegularityLaw W` for a finite set $W$ of places of `modularFunctionFieldC k N`, each supersingular in the sense of `ssPlaces q N k`. Let $K\subset\overline{\mathbb{Q}}$ be a finite extension of $\mathbb{Q}$, let $w\in W$, and assume every $a\in k$ with $a^{q^{2}}=a$ lies in the image of $A\cap K$ under $\mathrm{red}$. Then for every $g$ in the subring `R.nodeIntegersOver K w` of elements of `R.nodeIntegers w` whose Laurent series lies in `NodeLocalized.fieldOver (N * q) K`, there is $o\in A\cap K$ such that $g-$`R.nodeConst K w o`, the constant with value $o$, is not a unit of that subring.
--
--   This is the residue surjectivity (rationality over the residue field of $A\cap K$) of the node ring attached to a supersingular crossing of the model of $X_0(Nq)$, expressed inside the function field via a prolongation tuple: the maximal ideal of the node ring is reached by subtracting a constant from $A\cap K$. It feeds the results that produce node packages, unique lifts of places with prescribed values, and inertia-fixed presentations of node coordinates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_not_isUnit_sub_nodeConst_of_evalAt_mem_range_redRestrict_of_orderLawFixed.lean

import Definitions.Def_ModularCurve_NodeLocalizedPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_not_isUnit_sub_nodeConst_of_evalAt_mem_range_redRestrict_of_orderLawFixed
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (hord : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
    (hk₀ : ∀ a : k, a ^ (q ^ 2) = a → a ∈ Set.range (NodeLocalized.redRestrict red K))
    (g : ↥(R.nodeIntegersOver K w)) :
    ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o) := by sorry
