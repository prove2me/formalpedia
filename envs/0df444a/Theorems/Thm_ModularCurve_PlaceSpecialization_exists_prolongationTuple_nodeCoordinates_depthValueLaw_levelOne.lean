-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_prolongationTuple_nodeCoordinates_depthValueLaw_levelOne
-- name    : ModularCurve.PlaceSpecialization.exists_prolongationTuple_nodeCoordinates_depthValueLaw_levelOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/ff05a2ef-d82a-51df-8395-c815a9c119eb
-- title:
--   Level-one prolongation tuple with node coordinates and depth
-- statement:
--   Fix a prime $q$ with $5 \le q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $\mathrm{red} : A \to k$, modular polynomial data `data` for $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the $q$-expansion pair) whose reduction modulo $q$ is $(\mathrm{C}X^{q} - X)(\mathrm{C}X - X^{q})$, integrality hypotheses $h\alpha, h\beta$ for the two maps `heckeAlphaBar`, `heckeBetaBar` from level $1$ to level $q$ over $\overline{\mathbb{Q}}$, and a place specialisation $P$ of the level-one situation. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\,k\,1$ whose members are exactly the supersingular places (rational, affine geometric, with $j$-value in $\mathrm{ssJSet}$), and let $e$ satisfy $e(w) = \mathrm{jWidth}(w(\,j\,))$ for $w \in W$, i.e. $3$ at $j=0$, $2$ at $j=1728$ and $1$ otherwise. Then there is a prolongation tuple $R$ over $P$ — a pair of regular prolongations $R_1, R_2$ of the level-$q$ function field with their residue maps, compatible with $\mathrm{red}$ and the Atkin–Lehner involution — which is a model (the two divisor laws and the two cusp laws), satisfies the regularity law and node-value law on $W$ and the fixed-place order law, together with: a number field $K \subseteq \overline{\mathbb{Q}}$; an element $\varpi$ of $A \cap K$ whose multiples are exactly the kernel of the reduction of $A \cap K$ to $k$; an integer $e_K \ge 1$ and a unit $\varepsilon$ of $A \cap K$ with $q = \varpi^{e_K}\varepsilon$; for each $w \in W$ node coordinates $(x_w, y_w)$ in the ring $\mathcal{O}_w$ of functions integral for $R_1$, $R_2$ and for all places above $w$ and defined over $K$, normalised by $\mathrm{res}_1(x_w) = 0$, $\mathrm{ord}_{\mathrm{Frob}\cdot w}\,\mathrm{res}_2(x_w) = 1$, $\mathrm{res}_2(y_w) = 0$, $\mathrm{ord}_w\,\mathrm{res}_1(y_w) = 1$; and a function $\mathrm{depth}$ from places of the level-$q$ function field over $\overline{\mathbb{Q}}$ to $\mathbb{N}$, such that for every $w \in W$: $x_w y_w = \varpi^{e(w) e_K} u$ for a unit $u$ of $\mathcal{O}_w$ (with $\varpi$ viewed as a constant function); the ideal $(\varpi, x_w, y_w)$ is maximal and is the only maximal ideal of $\mathcal{O}_w$; the ideals $(\varpi, x_w)$ and $(\varpi, y_w)$ are prime with $y_w \notin (\varpi, x_w)$ and $x_w \notin (\varpi, y_w)$; $\mathcal{O}_w$ is Noetherian; every $g \in \mathcal{O}_w$ differs from some constant from $A \cap K$ by a non-unit; the value-integrality law holds at $w$, i.e. every function integral at $w$ takes values in $A$ at every place above $w$; and for every place $V$ above $w$ fixed by the inertia subgroup of $A$ over $\mathbb{Q}$ acting through the arithmetic Galois action, the $A$-valuation of $y_w(V)$ equals the $A$-valuation of $q$ raised to the power $\mathrm{depth}(V)$.
--
--   This packages, at level one, the local data at the supersingular points of the regular model of $X_0(q)$ in characteristic $q$: the two Gauss prolongations with their divisor, cusp, regularity and order laws, the crossing presentation $xy = \varpi^{e \cdot e_K}$ of the node ring with its unique maximal ideal and two branches, and the integrality of the $q$-adic depth of inertia-fixed points. It is consumed by [`ModularCurve.exists_componentHom_extension_of_dRModelPackage_of_abelJacobi_of_ffPin`](thm.html#ModularCurve.exists_componentHom_extension_of_dRModelPackage_of_abelJacobi_of_ffPin) in the construction of the component-group homomorphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_prolongationTuple_nodeCoordinates_depthValueLaw_levelOne.lean

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

theorem ModularCurve.PlaceSpecialization.exists_prolongationTuple_nodeCoordinates_depthValueLaw_levelOne
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (hq : 5 ≤ q)
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Finset (Place k (modularFunctionFieldC k 1)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k)
    (e : Place k (modularFunctionFieldC k 1) → ℕ)
    (he : ∀ w ∈ W, e w = jWidth (w.evalAt (jGeomGen k 1))) :
    ∃ (R : ProlongationTuple P), R.IsModel ∧ R.RegularityLaw W ∧ R.NodeValueLaw W ∧ R.OrderLawFixed ∧
      ∃ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K)
        (ϖ : ↥(NodeLocalized.coeffSubring A K))
        (_ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
        (eK : ℕ) (_ : 1 ≤ eK) (ε : ↥(NodeLocalized.coeffSubring A K)) (_ : IsUnit ε)
        (_ : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε)
        (cs : ∀ w ∈ W, R.NodeCoordinates K w)
        (depth : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) → ℕ),
        (∀ w (hw : w ∈ W), ∃ u : ↥(R.nodeIntegersOver K w), IsUnit u ∧
            (cs w hw).x * (cs w hw).y = R.nodeConst K w ϖ ^ (e w * eK) * u) ∧
        (∀ w (hw : w ∈ W),
            (Ideal.span {R.nodeConst K w ϖ, (cs w hw).x, (cs w hw).y}).IsMaximal ∧
            ∀ M : Ideal ↥(R.nodeIntegersOver K w), M.IsMaximal → M = Ideal.span {R.nodeConst K w ϖ, (cs w hw).x, (cs w hw).y}) ∧
        (∀ w (hw : w ∈ W),
            (Ideal.span {R.nodeConst K w ϖ, (cs w hw).x}).IsPrime ∧ (Ideal.span {R.nodeConst K w ϖ, (cs w hw).y}).IsPrime ∧
            (cs w hw).y ∉ Ideal.span {R.nodeConst K w ϖ, (cs w hw).x} ∧ (cs w hw).x ∉ Ideal.span {R.nodeConst K w ϖ, (cs w hw).y}) ∧
        (∀ w ∈ W, IsNoetherianRing ↥(R.nodeIntegersOver K w)) ∧
        (∀ w ∈ W, ∀ g : ↥(R.nodeIntegersOver K w),
            ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o)) ∧
        (∀ w ∈ W, R.ValueIntegralityLaw w) ∧
        (∀ w (hw : w ∈ W), (cs w hw).DepthValueLaw depth) := by sorry
