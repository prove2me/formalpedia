-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_depthQ_cleared_law_and_forall_inertia_smul_eq_levelOne
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_depthQ_cleared_law_and_forall_inertia_smul_eq_levelOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/ac525e4f-6a02-5e6d-aa5a-cbb1cd2d596e
-- title:
--   Rational node depth: cleared law and inertia invariance
-- statement:
--   Let $q\ge 5$ be a prime, let $A$ be a valuation subring of $\overline{\mathbb Q}$, let $k$ be an algebraically closed field of characteristic $q$ and $\mathrm{red}:A\to k$ a ring homomorphism; let `data` be modular polynomial data for $q$ satisfying the Kronecker congruence `hKr`, and assume the two Hecke maps $\bar\alpha,\bar\beta$ from level $1$ to level $1\cdot q$ over $\overline{\mathbb Q}$ are integral. Let $P$ be a place-specialisation datum at level $1$ for these data (a map from places of the level-$1\cdot q$ geometric function field $\overline{\mathbb Q}$-fibre to places over $k$, together with a map on degree-zero divisor classes and the compatibilities with reduction of $j$ and $j_N$), and let $W$ be a finite set of places of `modularFunctionFieldC k 1` whose members are exactly the supersingular places `ssPlaces q 1 k`, i.e. the rational affine geometric places whose $j$-value lies in the supersingular set. Let $R$ be a prolongation tuple for $P$ satisfying the model law, the regularity and node-value laws at $W$, the fixed-order law, and the value-integrality law at each $w\in W$ (so that every element of $R$'s node integers at $w$ has $A$-integral value at every place $V$ with $P.\mathrm{reduceFst}\,V=w$). Assume given, for each place $w$, a finite extension $K_w\subseteq\overline{\mathbb Q}$ of $\mathbb Q$, fixed pointwise by the inertia subgroup of $A$ over $\mathbb Q$ whenever $w\in W$; node coordinates $(x_w,y_w)$ over $K_w$ at each $w\in W$ (elements of the node integers over $K_w$ with $x_w$ reducing to $0$ on the first branch and having order $1$ on the Frobenius translate of the second, and $y_w$ reducing to $0$ on the second branch and having order $1$ at $w$); a width $e_w\in\mathbb N$; elements $\varpi_w,\varepsilon_w$ of $A\cap K_w$ and integers $e_{K_w}\ge 1$ with $\varepsilon_w$ a unit and $q=\varpi_w^{e_{K_w}}\varepsilon_w$ in $A\cap K_w$ for $w\in W$; and units $u_w$ of the node integers over $K_w$ with $x_w y_w=\varpi_w^{\,e_w e_{K_w}}u_w$, the power of $\varpi_w$ being taken through the constant homomorphism `nodeConst`. The conclusion is the existence of a single rational-valued function $\delta$ on the places of the level-$1\cdot q$ function field over $\overline{\mathbb Q}$ such that: for every $w\in W$ and every place $V$ with $P.\mathrm{reduceFst}\,V=w$ that is neither strictly first nor strictly second in the sense of $P$, one has $0<\delta(V)<e_w$ and the cleared depth–value identity $v_A(y_w(V))^{\,\mathrm{den}\,\delta(V)}=v_A(q)^{\,\mathrm{num}\,\delta(V)}$ in the value group of $A$, where $v_A(y_w(V))$ is the valuation of the value of $y_w$ at $V$; and $\delta$ is invariant under the arithmetic Galois action of the inertia subgroup of $A$ over $\mathbb Q$ on all places.
--
--   This supplies the depth function measuring, in units of $v_A(q)$, how far a point of the open annulus lying over a supersingular crossing of the reduction of $X_0(q)$ sits from either branch, in the form of a rational number with cleared denominators; the bounds $0<\delta<e_w$ record that the point lies strictly inside the annulus of width $e_w$. It is the input for the orbit version of the annulus specialisation datum at level one, and is used in the construction of the annulus data laws.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_depthQ_cleared_law_and_forall_inertia_smul_eq_levelOne.lean

import Mathlib
import Definitions.Def_ModularCurve_NodeDepth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_depthQ_cleared_law_and_forall_inertia_smul_eq_levelOne
    {q : ℕ} [Fact q.Prime] (hq5 : 5 ≤ q) {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    {W : Finset (Place k (modularFunctionFieldC k 1))}
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (hO : R.OrderLawFixed) (hVI : ∀ w ∈ W, R.ValueIntegralityLaw w)
    (K : Place k (modularFunctionFieldC k 1) → IntermediateField ℚ (AlgebraicClosure ℚ))
    [hK : ∀ w : Place k (modularFunctionFieldC k 1), FiniteDimensional ℚ ↥(K w)]
    (hKfix : ∀ w ∈ W, ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ z ∈ K w, σ z = z)
    (coord : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W), R.NodeCoordinates (K w) w)
    (width : Place k (modularFunctionFieldC k 1) → ℕ)
    (ϖ : ∀ w : Place k (modularFunctionFieldC k 1), ↥(NodeLocalized.coeffSubring A (K w)))
    (eK : Place k (modularFunctionFieldC k 1) → ℕ) (heK : ∀ w ∈ W, 1 ≤ eK w)
    (ε : ∀ w : Place k (modularFunctionFieldC k 1), ↥(NodeLocalized.coeffSubring A (K w)))
    (hε : ∀ w ∈ W, IsUnit (ε w))
    (hqϖ : ∀ w ∈ W, ((q : ℕ) : ↥(NodeLocalized.coeffSubring A (K w))) = ϖ w ^ eK w * ε w)
    (u : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W), ↥(R.nodeIntegersOver (K w) w))
    (hu : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W), IsUnit (u w hw) ∧
        (coord w hw).x * (coord w hw).y = R.nodeConst (K w) w (ϖ w) ^ (width w * eK w) * u w hw) :
    ∃ depthQ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) → ℚ,
      (∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))),
        P.reduceFst V = w → ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V →
          0 < depthQ V ∧ depthQ V < width w ∧ (coord w hw).yDepth V ^ (depthQ V).den =
            A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ^ (depthQ V).num.toNat) ∧
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
        depthQ (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V) = depthQ V) := by sorry
