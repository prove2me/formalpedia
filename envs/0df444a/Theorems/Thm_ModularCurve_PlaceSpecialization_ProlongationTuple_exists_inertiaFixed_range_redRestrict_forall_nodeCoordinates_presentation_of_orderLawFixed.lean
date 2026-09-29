-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_inertiaFixed_range_redRestrict_forall_nodeCoordinates_presentation_of_orderLawFixed
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_inertiaFixed_range_redRestrict_forall_nodeCoordinates_presentation_of_orderLawFixed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/4f638433-b209-5a2a-8bf3-b29aa6450db5
-- title:
--   Inertia-fixed node presentation at supersingular places of X₀(Nq)
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbf Q}$, a level $N\ge 1$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $\mathrm{red}\colon A\to k$, modular polynomial data `data` for $q$ satisfying the Kronecker congruence `hKr`, integrality hypotheses $h\alpha,h\beta$ for the two degeneracy embeddings at level $N,q$, a place specialisation $P$ and a prolongation tuple $R$ over $P$. Assume $q\nmid N$; that $\mathrm{red}$ has kernel exactly the maximal ideal of $A$; that $R$ is a model (the two divisor laws and the two cusp laws) and satisfies the fixed-place order law; and that $W$ is a finite set of places of $\mathrm{modularFunctionFieldC}\,k\,N$, each rational, affine and with supersingular $j$-invariant, for which $R$ satisfies the regularity law and the node-value law. Then there is a number field $K_0\subseteq\overline{\mathbf Q}$ such that: every element of the inertia subgroup $A.\mathrm{inertiaSubgroupIn}\,\mathbb Q$ fixes $K_0$ pointwise; the restriction of $\mathrm{red}$ to $A\cap K_0$ kills exactly the multiples of $q$; every $a\in k$ with $a^{q^2}=a$ lies in the image of that restriction; and there are node coordinates $(x_w,y_w)$ over $K_0$ at each $w\in W$, i.e. elements of the node ring $R.\mathrm{nodeIntegersOver}\,K_0\,w$ with $x_w$ in the kernel of the first node residue and of order $1$ for the second residue at $\mathrm{arithFrobC}\cdot w$, and symmetrically for $y_w$, satisfying: $x_wy_w=q^{\,\mathrm{placeWidthChar}\,q\,N\,w}u_w$ with $u_w$ a unit; $(q,x_w,y_w)$ is maximal and is the only maximal ideal; $(q,x_w)$ and $(q,y_w)$ are prime with $y_w\notin(q,x_w)$ and $x_w\notin(q,y_w)$; the node ring is Noetherian; and for every $g$ in it some $o\in A\cap K_0$ makes $g-o$ a non-unit.
--
--   This is the characteristic-$q$ crossing presentation of $X_0(Nq)$ at the supersingular nodes, realised simultaneously for all places in $W$ over a single inertia-fixed number field whose coefficient ring reduces onto $\mathbf F_{q^2}$, so that supersingular $j$-values and their Frobenius images are hit. It feeds the variant of the statement without the $\mathbf F_{q^2}$-range clause and the packages recording widths, depths and the component-group computation at level $N$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_inertiaFixed_range_redRestrict_forall_nodeCoordinates_presentation_of_orderLawFixed.lean

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_PlaceWidthChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing
open ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_inertiaFixed_range_redRestrict_forall_nodeCoordinates_presentation_of_orderLawFixed
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P) (hqN : ¬ q ∣ N)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (hR : R.IsModel) (hO : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W) :
    ∃ (K₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ ↥K₀),
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ z ∈ K₀, σ z = z) ∧
      (∀ d : ↥(NodeLocalized.coeffSubring A K₀),
        NodeLocalized.redRestrict red K₀ d = 0 ↔ ∃ d', d = ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)) * d') ∧
      (∀ a : k, a ^ (q ^ 2) = a → a ∈ Set.range (NodeLocalized.redRestrict red K₀)) ∧
      ∃ (cs : ∀ w ∈ W, R.NodeCoordinates K₀ w),
        (∀ w (hw : w ∈ W), ∃ u : ↥(R.nodeIntegersOver K₀ w), IsUnit u ∧
          (cs w hw).x * (cs w hw).y =
            R.nodeConst K₀ w ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)) ^ placeWidthChar q N w * u) ∧
        (∀ w (hw : w ∈ W),
          (Ideal.span {R.nodeConst K₀ w ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)), (cs w hw).x, (cs w hw).y}).IsMaximal ∧
          ∀ M : Ideal ↥(R.nodeIntegersOver K₀ w), M.IsMaximal →
            M = Ideal.span {R.nodeConst K₀ w ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)), (cs w hw).x, (cs w hw).y}) ∧
        (∀ w (hw : w ∈ W),
          (Ideal.span {R.nodeConst K₀ w ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)), (cs w hw).x}).IsPrime ∧
          (Ideal.span {R.nodeConst K₀ w ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)), (cs w hw).y}).IsPrime ∧
          (cs w hw).y ∉ Ideal.span {R.nodeConst K₀ w ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)), (cs w hw).x} ∧
          (cs w hw).x ∉ Ideal.span {R.nodeConst K₀ w ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K₀)), (cs w hw).y}) ∧
        (∀ w ∈ W, IsNoetherianRing ↥(R.nodeIntegersOver K₀ w)) ∧
        (∀ w ∈ W, ∀ g : ↥(R.nodeIntegersOver K₀ w),
          ∃ o : ↥(NodeLocalized.coeffSubring A K₀), ¬ IsUnit (g - R.nodeConst K₀ w o)) := by sorry
