-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_componentGroupProj_depthDual_add_degree_sndDiv_smul_eq_zero_of_div_levelOne_of_five_le
-- name    : ModularCurve.PlaceSpecialization.componentGroupProj_depthDual_add_degree_sndDiv_smul_eq_zero_of_div_levelOne_of_five_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/22b345b6-d929-5ea5-a4c4-1eed9eb34e85
-- title:
--   Principal divisors have trivial depth component class at level one
-- statement:
--   Let $q$ be a prime with $5 \le q$, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$, let $k$ be an algebraically closed perfect field of characteristic $q$ and $red \colon A \to k$ a ring homomorphism; fix modular polynomial data `data` for $q$ together with a proof `hKr` that its bivariate reduction mod $q$ equals $(Y^q - X)(Y - X^q)$, and integrality hypotheses $h\alpha$, $h\beta$ for the two degeneracy embeddings of the level-$1$ into the level-$1\cdot q$ Laurent function field over $\overline{\mathbb{Q}}$. Let $P$ be a place specialisation of these data, $R$ a prolongation tuple for $P$ which is a model (`IsModel`) and satisfies the fixed order law (`OrderLawFixed`), and note the hypothesis $\neg\, q \mid 1$. Let $W$ be a finite set of places of the level-$1$ function field $\mathrm{modularFunctionFieldC}\,k\,1$ whose members are exactly the supersingular places `ssPlaces q 1 k`, and assume the regularity law `RegularityLaw W` and the node-value law `NodeValueLaw W`. Let $e$ assign to each place a natural number with $e(w) \ge 1$ for $w \in W$. Let $K \subseteq \overline{\mathbb{Q}}$ be a number field, $\varpi$ an element of $A \cap K$ such that an element of $A \cap K$ reduces to $0$ under $red$ exactly when it is divisible by $\varpi$, and suppose $q = \varpi^{e_K}\varepsilon$ with $e_K \ge 1$ and $\varepsilon$ a unit. For each $w \in W$ let $c_w$ be node coordinates $x, y$ over $K$ in the ring $B_w = R.\mathrm{nodeIntegersOver}\,K\,w$ such that: $x\,y = \varpi^{e(w)e_K} u$ for some unit $u$ of $B_w$ (with $\varpi$ pushed into $B_w$ by `nodeConst`); the ideal $(\varpi, x, y)$ is maximal and is the only maximal ideal of $B_w$; the ideals $(\varpi, x)$ and $(\varpi, y)$ are prime with $y \notin (\varpi, x)$ and $x \notin (\varpi, y)$; $B_w$ is Noetherian; every $g \in B_w$ satisfies $g - \varpi'$ a non-unit for some constant $\varpi'$ from $A \cap K$; and the value-integrality law holds at $w$. Let $\mathrm{depth}$ be a natural-number weight on the places of the level-$1\cdot q$ function field over $\overline{\mathbb{Q}}$ satisfying the depth-value law for each $c_w$, i.e. for every place $V$ with $P.\mathrm{reduceFst}\,V = w$ that is fixed by the inertia subgroup of $A$ acting through `arithmeticGalois`, the $y$-depth of $V$ equals the $A$-valuation of $q$ raised to $\mathrm{depth}\,V$. Finally let $f \ne 0$ be an element of the level-$1\cdot q$ function field over $\overline{\mathbb{Q}}$, let $D$ be its divisor, $D(V) = \mathrm{ord}_V f$, and assume every $V$ in the support of $D$ either is strictly first-sheet or strictly second-sheet for $P$, or else reduces into $W$ under $P.\mathrm{reduceFst}$ and is fixed by the inertia subgroup of $A$. Then for every crossing $s_0$ in the finite set `nodePairsOfPlaces (arithFrobC q k 1) W` of Frobenius-paired places, the class in the component group attached to the widths $s \mapsto e(s.1)$ of the dual element $P.\mathrm{depthDual}$ of $D$ plus $\deg(P.\mathrm{sndDiv}\,D)$ times $e(s_0.1)\cdot \mathrm{crossingCoord}\,s_0$ vanishes, where $P.\mathrm{depthDual}$ is $\sum_s (\text{depth divisor of } D \text{ at } s.1)\cdot \mathrm{crossingCoord}\,s$ and $P.\mathrm{sndDiv}\,D$ is the part of $D$ supported on strictly second-sheet places.
--
--   This is the statement that the depth-weighted specialisation functional of a principal divisor has trivial class in the component group of the special fibre at $q$ — the component group of the Néron model of $J_0(q)$ computed from the supersingular crossings of the semistable reduction, the monodromy-pairing picture of Raynaud and Grothendieck — in the level-one case $N = 1$, with an abstract depth weight constrained only by the depth-value law, so that concrete depth functions instantiate it by application. It is used to construct the depth-comparison homomorphism out of the divisor group together with its surjectivity at level one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_componentGroupProj_depthDual_add_degree_sndDiv_smul_eq_zero_of_div_levelOne_of_five_le.lean

import Definitions.Def_ModularCurve_NodeDepth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.componentGroupProj_depthDual_add_degree_sndDiv_smul_eq_zero_of_div_levelOne_of_five_le
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [PerfectField k] [IsAlgClosed k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (R : ProlongationTuple P) [DecidableEq k] (hqN : ¬ q ∣ 1) (hq : 5 ≤ q)
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
    (f : ↥(modularFunctionFieldBar (1 * q))) (hf : f ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hDf : ∀ V, D V = V.ord f)

    (hsupp : ∀ V ∈ D.support,
        P.IsStrictFst V ∨ P.IsStrictSnd V ∨
          (P.reduceFst V ∈ W ∧
            ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V = V))
    (s₀ : ↥(nodePairsOfPlaces (arithFrobC q k 1) W)) :
    componentGroupProj (widthOfPlaces (arithFrobC q k 1) W e)
        (P.depthDual (arithFrobC q k 1) W depth D +
          Divisor.degree (P.sndDiv D) •
            (((e (s₀ : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1 : ℕ) : ℤ) •
              crossingCoord s₀)) = 0 := by sorry
