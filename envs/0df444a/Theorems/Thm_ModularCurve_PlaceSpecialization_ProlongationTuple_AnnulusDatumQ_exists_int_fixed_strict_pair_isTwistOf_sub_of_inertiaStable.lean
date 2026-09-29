-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_int_fixed_strict_pair_isTwistOf_sub_of_inertiaStable
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumQ.exists_int_fixed_strict_pair_isTwistOf_sub_of_inertiaStable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/984dee52-f78b-5b06-a258-424fb6b70779
-- title:
--   Twisting an inertia-stable divisor by a fixed strict pair
-- statement:
--   Let $q\ge 5$ be prime, let $A$ be a valuation subring of $\overline{\mathbf Q}$, let $k$ be an algebraically closed field of characteristic $q$ and $red:A\to k$ a ring homomorphism; let `data` be modular polynomial data for $q$ satisfying the Kronecker congruence (its reduction modulo $q$ is $(C X^q-X)(C X-X^q)$), let the two Hecke degeneracy embeddings at level $1$ and $q$ be integral, and let $P$ be a place specialization for these data. Let $W$ be a finite set of places of `modularFunctionFieldC k 1` whose members are exactly the supersingular places `ssPlaces q 1 k`, let $R$ be a prolongation tuple for $P$ satisfying `IsModel` (the two divisor laws and the two cusp laws), the regularity law and node-value law at $W$ and `OrderLawFixed`, and let `dat` be an orbit annulus datum for $R$ at $W$, consisting of coordinate fields $K(w)\subseteq\overline{\mathbf Q}$, node coordinates, widths, a rational depth function `depthQ` on places of `modularFunctionFieldBar (1*q)`, a cusp, uniformisers and units. Assume: every $w\in W$ has width $\ge 1$ equal to `jWidth` of the value of `jGeomGen k 1` at $w$ (so $3$, $2$ or $1$ according as that value is $0$, $1728$ or neither); the value-integrality law holds at each $w\in W$ (functions in `R.nodeIntegers w` have values in $A$ at all places above $w$); the inertia subgroup of $A$ over $\mathbf Q$ fixes each $K(w)$ pointwise; for $w\in W$ and each place $V$ with `reduceFst V = w` that is neither strict of the first nor of the second kind, $0<\mathrm{depthQ}(V)<\mathrm{width}(w)$ and the $y$-depth of $V$ raised to the denominator of $\mathrm{depthQ}(V)$ equals $A$'s valuation of $q$ raised to its numerator; and `depthQ` is invariant under the arithmetic Galois action of inertia. Let $E$ be a degree-zero divisor on `modularFunctionFieldBar (1*q)` fixed by the arithmetic Galois action of inertia and supported on places that are strict of the first kind, strict of the second kind, or reduce under `reduceFst` into $W$, and let $B$ be a finite set of places of `modularFunctionFieldC k 1`. Then there exist an integer $c$ and places $P_1,P_2$ of `modularFunctionFieldBar (1*q)` with $P_1$ strict of the first kind and $P_2$ strict of the second kind, with `reduceFst P₁ ∉ B` and `reduceSnd P₂ ∉ B`, both fixed by every element of the inertia subgroup, and a twist vector $a$ (integers `aZ`, `aZ'` and values `aE`) such that `dat.IsTwistOf a (E - c • (P₂ - P₁))` holds: the degrees of the strict-first and strict-second parts of $E-c(P_2-P_1)$ are minus the sums over $w\in W$ of the end orders attached to $a$ and that divisor, and for each $w\in W$ and each $d$ with $1\le d$ and $d+1\le \mathrm{width}(w)$ the tent-weighted circle degree $\sum_V (E-c(P_2-P_1))(V)\max(0,1-|\mathrm{depthQ}(V)-d|)$, over places $V$ over $w$ that are not strict of either kind, equals $-\bigl(a_{d-1}-2a_d+a_{d+1}\bigr)$ for the chain values of $a$ at $w$.
--
--   This is the component-group half of the reach statement for inertia-stable divisor classes: modulo the class of a single inertia-fixed pair of strict points, an inertia-stable divisor of degree zero with good support satisfies the twist equations of the orbit annulus specialization, i.e. its branch degrees and tent-weighted circle degrees are given by minus the discrete Laplacian of a twist vector. It is used in [`ModularCurve.PlaceSpecialization.exists_fixedStrict_kernelGood_principal`](thm.html#ModularCurve.PlaceSpecialization.exists_fixedStrict_kernelGood_principal), where the remaining, torus-type, half is supplied separately.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_int_fixed_strict_pair_isTwistOf_sub_of_inertiaStable.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_LevelOneAnnulusSpecializationOrbit
import Definitions.Def_ModularCurve_JWidth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization
open Classical in

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumQ.exists_int_fixed_strict_pair_isTwistOf_sub_of_inertiaStable
    {q : ℕ} [Fact q.Prime] (hq5 : 5 ≤ q) {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    {W : Finset (Place k (modularFunctionFieldC k 1))}
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (hO : R.OrderLawFixed)
    (dat : R.AnnulusDatumQ W)
    (hwidth : ∀ w ∈ W, 1 ≤ dat.width w)

    (hwidthj : ∀ w ∈ W, dat.width w = jWidth (w.evalAt (jGeomGen k 1)))
    (hVI : ∀ w ∈ W, R.ValueIntegralityLaw w)

    (hKfix : ∀ w ∈ W, ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ z ∈ dat.K w, σ z = z)

    (hdepthQ : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W)
        (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))),
        P.reduceFst V = w → ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V →
          0 < dat.depthQ V ∧ dat.depthQ V < dat.width w ∧ (dat.coord w hw).yDepth V ^ (dat.depthQ V).den =
            A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ^ (dat.depthQ V).num.toNat)
    (hdepthσ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
        dat.depthQ (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V) = dat.depthQ V)
    (E : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q)))))
    (hEstab : ∀ σ ∈ A.inertiaSubgroupIn ℚ,
        arithmeticGalois (modularFunctionFieldFull (1 * q)) σ •
          (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) = E)
    (hEsupp : ∀ V ∈ (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))).support,
        P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W)
    (B : Finset (Place k (modularFunctionFieldC k 1))) :
    ∃ (c : ℤ) (P₁ P₂ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))),
      P.IsStrictFst P₁ ∧ P.IsStrictSnd P₂ ∧ P.reduceFst P₁ ∉ B ∧ P.reduceSnd P₂ ∉ B ∧
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • P₁ = P₁) ∧
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • P₂ = P₂) ∧
      ∃ a : ProlongationTuple.TwistVector (k := k) W,
        dat.IsTwistOf a ((E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) -
            c • (Finsupp.single P₂ 1 - Finsupp.single P₁ 1)) := by sorry
