-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_depthQ_cleared_law_and_forall_inertia_smul_eq
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_depthQ_cleared_law_and_forall_inertia_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/117253dd-3f2c-51f5-86bb-d44554e473e7
-- title:
--   Inertia-invariant rational depth at supersingular nodes of X₀(Nq)
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a nonzero level $N$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $red : A \to k$, modular polynomial data `data` for $q$ together with a proof `hKr` that its bivariate reduction mod $q$ equals $(Y^q - X)(Y - X^q)$, and integrality data $h\alpha, h\beta$ for the two degeneracy embeddings of the base-changed level-$N$ function field into level $Nq$; let $P$ be a place specialisation for these data and assume $q \nmid N$. Let $W$ be a finite set of places of `modularFunctionFieldC k N`, each lying in `ssPlaces q N k`, i.e. rational, affine-geometric (both $j$ and $j_N$ in the valuation ring) and with supersingular $j$-value. Let $R$ be a prolongation tuple for $P$ satisfying the model laws (the two divisor laws and the two cusp laws), the regularity law and node-value law on $W$, the fixed-order law, and the value-integrality law at each $w \in W$ (every function in `R.nodeIntegers w` has $A$-integral value at every place $V$ with `P.reduceFst V = w`). Let $K$ assign to each place $w$ a finite extension $K_w$ of $\mathbb Q$ inside $\overline{\mathbb Q}$, fixed pointwise by the inertia subgroup `A.inertiaSubgroupIn ℚ` for $w \in W$, and for $w \in W$ let `coord w hw` be node coordinates $(x_w, y_w)$ over $K_w$ at $w$: elements of `R.nodeIntegersOver (K w) w` whose first residue kills $x_w$ while the second has order $1$ at $\mathrm{Frob} \cdot w$, and whose second residue kills $y_w$ while the first has order $1$ at $w$. Let `width`, `eK` be natural-number-valued functions with $eK_w \ge 1$ on $W$, and let $\varpi_w, \varepsilon_w \in A \cap K_w$ with $\varepsilon_w$ a unit and $q = \varpi_w^{eK_w}\varepsilon_w$ for $w \in W$; assume further that for $w \in W$ there is a unit $u_w$ of `R.nodeIntegersOver (K w) w` with $x_w y_w = (\varpi_w)^{\,\mathrm{width}_w \cdot eK_w} u_w$, the constant $\varpi_w$ being included through `R.nodeConst`. The conclusion asserts the existence of a single rational-valued function $\delta$ on the places $V$ of `modularFunctionFieldBar (N * q)` such that, first, whenever $w \in W$, `P.reduceFst V = w` and $V$ is neither `P.IsStrictFst` nor `P.IsStrictSnd`, one has $0 < \delta(V) < \mathrm{width}_w$ and, in the value group of $A$, the $y$-depth $v_A(V(y_w))$ raised to the denominator of $\delta(V)$ equals $v_A(q)$ raised to the numerator of $\delta(V)$; and second, $\delta$ is invariant under the action on places of `arithmeticGalois (modularFunctionFieldFull (N * q)) σ` for every $\sigma$ in `A.inertiaSubgroupIn ℚ`, for all places $V$.
--
--   This packages the depth of a point of the open annulus lying over a supersingular crossing of $X_0(Nq)$ as a single rational weight, measured in units of $v_A(q)$, together with the two properties its consumers require: the cleared depth–value equation with the bounds $0 < \delta < \mathrm{width}$, and invariance under the inertia group of $A$ over $\mathbb Q$. It is used by [`ModularCurve.PlaceSpecialization.ProlongationTuple.exists_annulusDatumLevel_laws`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.exists_annulusDatumLevel_laws) to supply the annulus datum at level $N$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_depthQ_cleared_law_and_forall_inertia_smul_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_NodeDepth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_depthQ_cleared_law_and_forall_inertia_smul_eq
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (hqN : ¬ q ∣ N)
    {W : Finset (Place k (modularFunctionFieldC k N))}
    (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (hO : R.OrderLawFixed) (hVI : ∀ w ∈ W, R.ValueIntegralityLaw w)
    (K : Place k (modularFunctionFieldC k N) → IntermediateField ℚ (AlgebraicClosure ℚ))
    [hK : ∀ w : Place k (modularFunctionFieldC k N), FiniteDimensional ℚ ↥(K w)]
    (hKfix : ∀ w ∈ W, ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ z ∈ K w, σ z = z)
    (coord : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W), R.NodeCoordinates (K w) w)
    (width : Place k (modularFunctionFieldC k N) → ℕ)
    (ϖ : ∀ w : Place k (modularFunctionFieldC k N), ↥(NodeLocalized.coeffSubring A (K w)))
    (eK : Place k (modularFunctionFieldC k N) → ℕ) (heK : ∀ w ∈ W, 1 ≤ eK w)
    (ε : ∀ w : Place k (modularFunctionFieldC k N), ↥(NodeLocalized.coeffSubring A (K w)))
    (hε : ∀ w ∈ W, IsUnit (ε w))
    (hqϖ : ∀ w ∈ W, ((q : ℕ) : ↥(NodeLocalized.coeffSubring A (K w))) = ϖ w ^ eK w * ε w)
    (u : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W), ↥(R.nodeIntegersOver (K w) w))
    (hu : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W), IsUnit (u w hw) ∧
        (coord w hw).x * (coord w hw).y = R.nodeConst (K w) w (ϖ w) ^ (width w * eK w) * u w hw) :
    ∃ depthQ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) → ℚ,
      (∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
        P.reduceFst V = w → ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V →
          0 < depthQ V ∧ depthQ V < width w ∧ (coord w hw).yDepth V ^ (depthQ V).den =
            A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ^ (depthQ V).num.toNat) ∧
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
        depthQ (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V) = depthQ V) := by sorry
