-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_comp_depthCompLaw_and_surjective_levelOne
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_comp_depthCompLaw_and_surjective_levelOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/d79b8a5c-7ee0-57db-9776-c8f827b25348
-- title:
--   Surjective depth–component homomorphism on inertia invariants, level one
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbf Q}$, an algebraically closed perfect field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$; fix modular polynomial data `data` for $q$ together with a witness `hKr` that its reduction modulo $q$ equals $(Y^q-X)(Y-X^q)$, and integrality witnesses $h\alpha$, $h\beta$ for the two Hecke embeddings from level $1$ to level $q$. Let $P$ be a place specialisation at level $N=1$ and $R$ a prolongation tuple over $P$, with $\lnot\, q \mid 1$, $R$ a model (the two divisor laws and the two cusp laws) and `R.OrderLawFixed`. Let $W$ be a finite set of places of the level-one geometric function field over $k$ whose members are exactly the supersingular places, and assume $R$ satisfies the regularity law and the node value law for $W$. Let $e$ be a width function with $e(w)\ge 1$ on $W$ and $e(w) =$ `jWidth` of the value of the geometric $j$-generator at $w$ (so $3$, $2$ or $1$ according as that value is $0$, $1728$, or neither). Let $K$ be a finite extension of $\mathbf Q$ inside $\overline{\mathbf Q}$, $\varpi$ an element of $A \cap K$ generating the kernel of the restricted reduction map, $e_K \ge 1$, $\varepsilon$ a unit with $q = \varpi^{e_K}\varepsilon$. At each $w \in W$ let node coordinates $x_w, y_w$ in the ring of node integers over $K$ be given, subject to: $x_w y_w = \varpi^{e(w)e_K}$ times a unit; the ideal $(\varpi, x_w, y_w)$ is maximal and is the only maximal ideal; $(\varpi, x_w)$ and $(\varpi, y_w)$ are prime with $y_w \notin (\varpi, x_w)$ and $x_w \notin (\varpi, y_w)$; the ring is Noetherian; every element differs from some constant by a non-unit; and the value integrality law holds at $w$. Let $depth$ be a natural-number-valued function on the places of the level-$q$ base-changed modular function field satisfying the depth value law for each system of node coordinates, and assume $5 \le q$. Assume finally that every inertia invariant class in $J^0$ at level $1\cdot q$ is $\mathrm{Pic}^0$ of a degree-zero divisor all of whose support points are fixed by the arithmetic Galois action of the inertia subgroup of $A$ over $\mathbf Q$ and are each strict of the first kind, strict of the second kind, or reduce under $P.\mathrm{reduceFst}$ into $W$. Then there is an additive homomorphism $comp$ from the inertia invariants of $J^0$ at level $1\cdot q$ to the component group of the width function attached to the arithmetic Frobenius semilinear automorphism, $W$ and $e$, which is surjective and satisfies `P.DepthCompLaw`: for every degree-zero divisor $D$ with inertia-invariant class and admissible inertia-fixed support, and every node pair $s_0$, $comp$ of that class is the image in the component group of the depth functional of $D$ plus $\deg(P.\mathrm{sndDiv}\,D)$ times $e(s_{0,1})$ times the crossing coordinate of $s_0$.
--
--   This is the construction, in the style of Raynaud and of the Mazur–Rapoport appendix, of the map from the inertia invariants of $J_0(q)(\overline{\mathbf Q})$ onto the component group of the special fibre at $q$, computed on admissible divisors by the depth functional of the Deligne–Rapoport model. It supplies the component-group homomorphism used by [`ModularCurve.exists_componentHom_extension_of_dRModelPackage_of_abelJacobi_of_ffPin`](thm.html#ModularCurve.exists_componentHom_extension_of_dRModelPackage_of_abelJacobi_of_ffPin).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_comp_depthCompLaw_and_surjective_levelOne.lean

import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_ModularCurve_ModularUnit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_comp_depthCompLaw_and_surjective_levelOne
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [PerfectField k] [IsAlgClosed k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (R : ProlongationTuple P) [DecidableEq k] (hqN : ¬ q ∣ 1)
    (hR : R.IsModel) (hO : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k 1)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k)
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W)
    (e : Place k (modularFunctionFieldC k 1) → ℕ) (he : ∀ w ∈ W, 1 ≤ e w)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (eK : ℕ) (heK : 1 ≤ eK) (ε : ↥(NodeLocalized.coeffSubring A K)) (hε : IsUnit ε)
    (hqϖ : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε)
    (cs : ∀ w ∈ W, R.NodeCoordinates K w)
    (hxy : ∀ w (hw : w ∈ W), ∃ u : ↥(R.nodeIntegersOver K w), IsUnit u ∧
        (cs w hw).x * (cs w hw).y = R.nodeConst K w ϖ ^ (e w * eK) * u)
    (hmax : ∀ w (hw : w ∈ W),
        (Ideal.span {R.nodeConst K w ϖ, (cs w hw).x, (cs w hw).y}).IsMaximal ∧
        ∀ M : Ideal ↥(R.nodeIntegersOver K w), M.IsMaximal → M = Ideal.span {R.nodeConst K w ϖ, (cs w hw).x, (cs w hw).y})
    (hbr : ∀ w (hw : w ∈ W),
        (Ideal.span {R.nodeConst K w ϖ, (cs w hw).x}).IsPrime ∧ (Ideal.span {R.nodeConst K w ϖ, (cs w hw).y}).IsPrime ∧
        (cs w hw).y ∉ Ideal.span {R.nodeConst K w ϖ, (cs w hw).x} ∧ (cs w hw).x ∉ Ideal.span {R.nodeConst K w ϖ, (cs w hw).y})
    (hnoeth : ∀ w ∈ W, IsNoetherianRing ↥(R.nodeIntegersOver K w))
    (hres : ∀ w ∈ W, ∀ g : ↥(R.nodeIntegersOver K w),
        ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o))
    (hVI : ∀ w ∈ W, R.ValueIntegralityLaw w)
    (depth : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) → ℕ)
    (hdepth : ∀ w (hw : w ∈ W), (cs w hw).DepthValueLaw depth)
    (hq : 5 ≤ q)
    (hwidth : ∀ w ∈ W, e w = jWidth (w.evalAt (jGeomGen k 1)))
    (hrep : ∀ x : ↥(inertiaInvariants A (1 * q)),
      ∃ D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q)))),
        Pic0.mk D = (x : JZero (1 * q)) ∧
        ∀ V ∈ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))).support,
          (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V = V) ∧
            (P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W)) :
    ∃ comp : ↥(inertiaInvariants A (1 * q)) →+ componentGroup (widthOfPlaces (arithFrobC q k 1) W e),
      P.DepthCompLaw (arithFrobC q k 1) W e depth comp ∧ Function.Surjective comp := by sorry
