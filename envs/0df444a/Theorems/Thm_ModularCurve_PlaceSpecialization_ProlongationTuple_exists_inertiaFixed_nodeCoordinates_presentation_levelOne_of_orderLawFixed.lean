-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_inertiaFixed_nodeCoordinates_presentation_levelOne_of_orderLawFixed
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_inertiaFixed_nodeCoordinates_presentation_levelOne_of_orderLawFixed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/16948f76-5843-53d5-a981-67b6fb69bc28
-- title:
--   Inertia-fixed node presentations at all supersingular places, level one
-- statement:
--   Let $q\ge 5$ be a prime, $A$ a valuation subring of $\overline{\mathbf Q}$, $k$ an algebraically closed field of characteristic $q$ and $\mathrm{red}\colon A\to k$ a ring homomorphism whose kernel is exactly the maximal ideal of $A$; let `data` be a modular polynomial datum for $q$ (a monic $\Phi\in\mathbf Z[X][Y]$ of degree $\psi(q)$ killing the $q$-expansion pair) satisfying the Kronecker congruence $\Phi\equiv (Y^q-X)(Y-X^q)$ mod $q$, let $h\alpha,h\beta$ be the integrality of the two degeneracy embeddings at level $1$ and prime $q$, let $P$ be a place specialization and $R$ a prolongation tuple over $P$ satisfying the model laws (the two divisor laws and the two cusp laws), the fixed-order law, and, for a finite set $W$ of places of $\mathrm{modularFunctionFieldC}\,k\,1$ all lying in $\mathrm{ssPlaces}\,q\,1\,k$ (rational affine geometric places whose $j$-value is supersingular), the regularity and node-value laws. Then there is a finite extension $K_0$ of $\mathbf Q$ inside $\overline{\mathbf Q}$ with: every element of the inertia subgroup of $A$ over $\mathbf Q$ fixes $K_0$ pointwise; an element $d$ of $A\cap K_0$ has $\mathrm{redRestrict}\,\mathrm{red}\,K_0\,d=0$ precisely when $d$ is a multiple of $q$; and for every $w\in W$ there are node coordinates $c=(c.x,c.y)$ over $K_0$ at $w$ and an element $u$ of $R.\mathrm{nodeIntegersOver}\,K_0\,w$ such that $u$ is a unit and $c.x\,c.y=\varpi^{\,\mathrm{jWidth}(w(j))\cdot 1}u$, where $\varpi$ denotes the image of $q$ under $R.\mathrm{nodeConst}\,K_0\,w$ and $\mathrm{jWidth}$ is $3$, $2$ or $1$ according as the value $w.\mathrm{evalAt}(\mathrm{jGeomGen}\,k\,1)$ is $0$, $1728$ or neither; moreover $(\varpi,c.x,c.y)$ is maximal and is the only maximal ideal of $R.\mathrm{nodeIntegersOver}\,K_0\,w$, the ideals $(\varpi,c.x)$ and $(\varpi,c.y)$ are prime with $c.y\notin(\varpi,c.x)$ and $c.x\notin(\varpi,c.y)$, the ring $R.\mathrm{nodeIntegersOver}\,K_0\,w$ is Noetherian, and every one of its elements $g$ admits $o\in A\cap K_0$ with $g-R.\mathrm{nodeConst}\,K_0\,w\,o$ not a unit.
--
--   This packages, uniformly over all supersingular places of the level-one curve and over a single inertia-fixed number field $K_0$ in which $q$ itself generates the relevant maximal ideal, the local description of $X_0(q)$ in characteristic $q$ as two branches crossing transversally, with crossing exponent given by the width attached to the $j$-invariants $0$ and $1728$. It is used by [`ModularCurve.PlaceSpecialization.ProlongationTuple.exists_annulusDatumQ_laws_levelOne`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.exists_annulusDatumQ_laws_levelOne), where each conjunct supplies one hypothesis of the annulus/orbit datum at level one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_inertiaFixed_nodeCoordinates_presentation_levelOne_of_orderLawFixed.lean

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_JWidth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_inertiaFixed_nodeCoordinates_presentation_levelOne_of_orderLawFixed
    {q : ℕ} [Fact q.Prime] (hq5 : 5 ≤ q) {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : ProlongationTuple P)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (hR : R.IsModel) (hO : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k 1))) (hW : ∀ w ∈ W, w ∈ ssPlaces q 1 k)
    (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W) :
    ∃ (K₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ ↥K₀),
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ z ∈ K₀, σ z = z) ∧
      (∀ d : ↥(NodeLocalized.coeffSubring A K₀),
        NodeLocalized.redRestrict red K₀ d = 0 ↔ ∃ d', d = ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)) * d') ∧
      ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W),
        ∃ (c : R.NodeCoordinates K₀ w) (u : ↥(R.nodeIntegersOver K₀ w)),
          (IsUnit (u) ∧
        c.x * c.y = R.nodeConst K₀ w ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)) ^ (jWidth (w.evalAt (jGeomGen k 1)) * 1) * u) ∧
          ((Ideal.span {R.nodeConst K₀ w ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)), c.x, c.y}).IsMaximal ∧
        ∀ M : Ideal ↥(R.nodeIntegersOver K₀ w), M.IsMaximal →
          M = Ideal.span {R.nodeConst K₀ w ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)), c.x, c.y}) ∧
          ((Ideal.span {R.nodeConst K₀ w ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)), c.x}).IsPrime ∧
        (Ideal.span {R.nodeConst K₀ w ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)), c.y}).IsPrime ∧
        c.y ∉ Ideal.span {R.nodeConst K₀ w ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)), c.x} ∧
        c.x ∉ Ideal.span {R.nodeConst K₀ w ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)), c.y}) ∧
          IsNoetherianRing ↥(R.nodeIntegersOver K₀ w) ∧
          (∀ g : ↥(R.nodeIntegersOver K₀ w),
        ∃ o : ↥(NodeLocalized.coeffSubring A K₀), ¬ IsUnit (g - R.nodeConst K₀ w o)) := by sorry
