-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_crossingPresentation_nodeIntegersOver_of_orderLawFixed_of_saturated
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_crossingPresentation_nodeIntegersOver_of_orderLawFixed_of_saturated
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/ae850fa1-eefb-505f-9675-f7296f618f7f
-- title:
--   Crossing presentation of the K-node ring at a supersingular node
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, an integer $N \ge 1$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$; fix modular polynomial data $data$ for $q$ (a monic $\Phi$ of degree $\psi(q)$ with $\Phi(j,j_q)=0$) satisfying the Kronecker congruence $\Phi \bmod q = (X_C^{\,q}-X)(X_C-X^{q})$, integrality hypotheses $h\alpha$, $h\beta$ for the two degeneracy maps $\overline{\alpha}$, $\overline{\beta}$ at level $N\,q$, a place specialisation $P$ and a prolongation tuple $R$ for $P$. Assume $q \nmid N$, that $R$ satisfies `IsModel` (the two divisor laws and the two cusp laws), the order law `OrderLawFixed` at places fixed by the square of geometric Frobenius, and the laws `RegularityLaw` and `NodeValueLaw` on a finite set $W$ of places of $\mathrm{modularFunctionFieldC}\,k\,N$ all of which are supersingular (rational, affine for $j$ and $j_N$, with $j$-value in $\mathrm{ssJSet}\,q\,k$). Fix a number field $K \subseteq \overline{\mathbb{Q}}$, a place $w \in W$, and assume the two residue maps of the node ring $R.\mathrm{nodeIntegersOver}\,K\,w$ are saturated: on the first branch, if $\mathrm{nodeResidue}_1(g)$ has positive order at $w$ and $\mathrm{nodeResidue}_1(g')$ has order $1$ there, then $\mathrm{nodeResidue}_1(g) = \mathrm{nodeResidue}_1(g')\,\mathrm{nodeResidue}_1(b)$ for some $b$ in that ring, and likewise on the second branch with orders measured at $\mathrm{arithFrobC}\,q\,k\,N \cdot w$. Let $c_0$ be a node-coordinate datum over $K$ at $w$, and let $\varpi \in A \cap K$ generate the kernel of the reduction $A\cap K \to k$, in the sense that $d$ reduces to $0$ precisely when $d \in \varpi\,(A\cap K)$. Then there is a node-coordinate datum $c$ with $(\varpi, c.x) = (\varpi, c_0.x)$ and $(\varpi, c.y) = (\varpi, c_0.y)$ as ideals of the node ring ($\varpi$ taken through the constants homomorphism `nodeConst`), there are $e_K \ge 1$ and a unit $\varepsilon$ of $A \cap K$ with $q = \varpi^{e_K}\varepsilon$, and there are $E \ge 1$ and a unit $u$ of the node ring with $c.x\,c.y = \varpi^{E} u$, such that $(\varpi, c.x, c.y)$ is maximal and is the only maximal ideal of the node ring, $(\varpi, c.x)$ and $(\varpi, c.y)$ are prime, and $c.y \notin (\varpi, c.x)$, $c.x \notin (\varpi, c.y)$.
--
--   This is the local crossing (node) presentation of the ring of $K$-rational functions integral at a supersingular point of the special fibre of $X_0(Nq)$ at $q$: the two branches meet transversally, the ring has a single maximal ideal, and the product of the two branch coordinates is a uniformiser power times a unit. It feeds the construction of node packages, the identification of the completion of the node ring with a $uv$-crossing model, and the inertia-fixed form of node coordinates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_crossingPresentation_nodeIntegersOver_of_orderLawFixed_of_saturated.lean

import Definitions.Def_ModularCurve_NodeLocalizedPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing
open ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_crossingPresentation_nodeIntegersOver_of_orderLawFixed_of_saturated
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (hmodel : R.IsModel) (hO : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
    (hsat₁ : ∀ g g' : ↥(R.nodeIntegersOver K w),
      0 < w.ord (R.nodeResidue₁ w ⟨g, g.2.1⟩) → w.ord (R.nodeResidue₁ w ⟨g', g'.2.1⟩) = 1 →
      ∃ b : ↥(R.nodeIntegersOver K w),
        R.nodeResidue₁ w ⟨g, g.2.1⟩ = R.nodeResidue₁ w ⟨g', g'.2.1⟩ * R.nodeResidue₁ w ⟨b, b.2.1⟩)
    (hsat₂ : ∀ g g' : ↥(R.nodeIntegersOver K w),
      0 < (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨g, g.2.1⟩) →
      (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨g', g'.2.1⟩) = 1 →
      ∃ b : ↥(R.nodeIntegersOver K w),
        R.nodeResidue₂ w ⟨g, g.2.1⟩ = R.nodeResidue₂ w ⟨g', g'.2.1⟩ * R.nodeResidue₂ w ⟨b, b.2.1⟩)
    (c₀ : R.NodeCoordinates K w)
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d') :
    ∃ c : R.NodeCoordinates K w,
      Ideal.span {R.nodeConst K w ϖ, c.x} = Ideal.span {R.nodeConst K w ϖ, c₀.x} ∧
      Ideal.span {R.nodeConst K w ϖ, c.y} = Ideal.span {R.nodeConst K w ϖ, c₀.y} ∧
    ∃ (eK : ℕ) (ε : ↥(NodeLocalized.coeffSubring A K)), 1 ≤ eK ∧ IsUnit ε ∧
      ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε ∧
    ∃ (E : ℕ) (u : ↥(R.nodeIntegersOver K w)), 1 ≤ E ∧ IsUnit u ∧ c.x * c.y = R.nodeConst K w ϖ ^ E * u ∧
      (Ideal.span {R.nodeConst K w ϖ, c.x, c.y}).IsMaximal ∧
      (∀ M : Ideal ↥(R.nodeIntegersOver K w), M.IsMaximal → M = Ideal.span {R.nodeConst K w ϖ, c.x, c.y}) ∧
      (Ideal.span {R.nodeConst K w ϖ, c.x}).IsPrime ∧ (Ideal.span {R.nodeConst K w ϖ, c.y}).IsPrime ∧
      c.y ∉ Ideal.span {R.nodeConst K w ϖ, c.x} ∧ c.x ∉ Ideal.span {R.nodeConst K w ϖ, c.y} := by sorry
