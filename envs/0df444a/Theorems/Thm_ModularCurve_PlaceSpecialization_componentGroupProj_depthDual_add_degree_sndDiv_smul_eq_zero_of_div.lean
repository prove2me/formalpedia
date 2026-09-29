-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_componentGroupProj_depthDual_add_degree_sndDiv_smul_eq_zero_of_div
-- name    : ModularCurve.PlaceSpecialization.componentGroupProj_depthDual_add_degree_sndDiv_smul_eq_zero_of_div
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/aea236ee-9852-5d3f-91bb-206ba942ed26
-- title:
--   Principal divisors have trivial depth class in the component group
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, an $N\ge 1$, an algebraically closed perfect field $k$ of characteristic $q$, a ring homomorphism $red\colon A\to k$, modular-polynomial data for $q$ (a monic $\Phi\in\mathbb Z[Y][X]$ of degree $\psi(q)$ annihilating the pair $(j,j_q)$) satisfying the Kronecker congruence $\Phi\equiv (Y^q-X)(Y-X^q)$ modulo $q$, and integrality of the two degeneracy embeddings `heckeAlphaBar`, `heckeBetaBar` of the level-$N$ into the level-$Nq$ function field over $\overline{\mathbb Q}$. Let $P$ be a `PlaceSpecialization` for these data (a specialisation map on places of the level-$N$ function field together with a map on degree-zero divisor classes, subject to the structure's $j$-compatibilities) and $R$ a `ProlongationTuple` over $P$, with $q\nmid N$, $R$ a model (`IsModel`) satisfying the fixed-place order law. Let $W$ be a finite set of places of `modularFunctionFieldC k N` whose members are exactly the supersingular places, with the regularity law and the node-value law for $W$, and let $e$ assign to each $w\in W$ an integer $e(w)\ge 1$. Let $K\subset\overline{\mathbb Q}$ be a number field, $\varpi\in A\cap K$ generating the kernel of the reduction $A\cap K\to k$ in the sense that $d$ reduces to $0$ exactly when $d\in\varpi\,(A\cap K)$, and $q=\varpi^{e_K}\varepsilon$ with $e_K\ge 1$ and $\varepsilon$ a unit. Assume given, for each $w\in W$, node coordinates $x_w,y_w$ over $K$ in the ring $B_w$ of node integers over $K$ at $w$ (so the first residue of $x_w$ vanishes, the second residue of $x_w$ has order $1$ at the Frobenius translate of $w$, the second residue of $y_w$ vanishes, the first residue of $y_w$ has order $1$ at $w$) such that $x_wy_w=\varpi^{e(w)e_K}u_w$ with $u_w\in B_w^\times$, such that $(\varpi,x_w,y_w)$ is maximal and is the only maximal ideal of $B_w$, such that $(\varpi,x_w)$ and $(\varpi,y_w)$ are prime with $y_w\notin(\varpi,x_w)$ and $x_w\notin(\varpi,y_w)$, such that $B_w$ is Noetherian, such that every $g\in B_w$ has $g-o$ a non-unit for some constant $o\in A\cap K$, and such that the value-integrality law holds at $w$. Let $depth$ be a natural-number weight on places of the level-$Nq$ function field over $\overline{\mathbb Q}$ satisfying, for every $w\in W$, the depth-value law for the node coordinates at $w$: for each place $V$ with $reduceFst(V)=w$ fixed by the inertia subgroup of $A$ acting through `arithmeticGalois`, the $y$-depth of $V$ equals the $A$-valuation of $q$ raised to $depth(V)$. Finally let $f\ne 0$ be an element of the level-$Nq$ function field over $\overline{\mathbb Q}$, $D$ the divisor with $D(V)=\operatorname{ord}_V f$ for all $V$, and assume every $V$ in the support of $D$ is strictly of the first sheet, or strictly of the second sheet, or else has $reduceFst(V)\in W$ and is fixed by the whole inertia subgroup of $A$. Then for every $s_0$ in the set of node pairs $\{(w,\,\mathrm{Frob}\cdot w):w\in W\}$, the element $$P.depthDual(\mathrm{Frob},W,depth,D)+\deg(P.sndDiv\,D)\cdot\bigl(e(s_0{}_{,1})\cdot crossingCoord(s_0)\bigr)$$ of the $\mathbb Z$-dual of the character lattice of the node-pair index set maps to $0$ under the projection to the component group attached to the width function $s\mapsto e(s_1)$, i.e. it lies in the image of the Gram map of the width pairing. Here `depthDual` is $\sum_s depthDiv(depth,D)(s_1)\cdot crossingCoord(s)$, `sndDiv` is the restriction of $D$ to the places strictly of the second sheet, and $crossingCoord(s)$ is the $s$-th coordinate functional restricted to the character lattice.
--
--   This is the principal-divisor law for the depth-weighted specialisation functional computing the group of connected components of the Néron model of $J_0(Nq)$ at $q$: the class attached to $\operatorname{div} f$, corrected by the degree of its second-sheet part, vanishes in the component group determined by the width pairing on supersingular crossing points. It is used in the construction of a depth function satisfying simultaneously the depth-composition, depth-value, second-degree, surjectivity and principality laws for a good width pinning.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_componentGroupProj_depthDual_add_degree_sndDiv_smul_eq_zero_of_div.lean

import Definitions.Def_ModularCurve_NodeDepth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.componentGroupProj_depthDual_add_degree_sndDiv_smul_eq_zero_of_div
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [PerfectField k] [IsAlgClosed k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : ProlongationTuple P) [DecidableEq k] (hqN : ¬ q ∣ N)
    (hR : R.IsModel) (hO : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W)
    (e : Place k (modularFunctionFieldC k N) → ℕ) (he : ∀ w ∈ W, 1 ≤ e w)
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
    (depth : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) → ℕ)
    (hdepth : ∀ w (hw : w ∈ W), (cs w hw).DepthValueLaw depth)
    (f : ↥(modularFunctionFieldBar (N * q))) (hf : f ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hDf : ∀ V, D V = V.ord f)

    (hsupp : ∀ V ∈ D.support,
        P.IsStrictFst V ∨ P.IsStrictSnd V ∨
          (P.reduceFst V ∈ W ∧
            ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V))
    (s₀ : ↥(nodePairsOfPlaces (arithFrobC q k N) W)) :
    componentGroupProj (widthOfPlaces (arithFrobC q k N) W e)
        (P.depthDual (arithFrobC q k N) W depth D +
          Divisor.degree (P.sndDiv D) •
            (((e (s₀ : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1 : ℕ) : ℤ) •
              crossingCoord s₀)) = 0 := by sorry
