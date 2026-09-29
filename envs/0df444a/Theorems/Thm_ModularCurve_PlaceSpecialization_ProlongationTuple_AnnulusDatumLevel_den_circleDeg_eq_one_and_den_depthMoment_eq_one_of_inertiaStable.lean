-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumLevel_den_circleDeg_eq_one_and_den_depthMoment_eq_one_of_inertiaStable
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumLevel.den_circleDeg_eq_one_and_den_depthMoment_eq_one_of_inertiaStable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/ec9c3fac-f34f-5d3a-8251-ace7301a116f
-- title:
--   Integrality of inertia-stable circle degrees and depth moments
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a positive integer $N$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$; fix modular polynomial data `data` for $q$ satisfying the Kronecker congruence `hKr`, integrality hypotheses $h\alpha$, $h\beta$ for the two degeneracy embeddings of the level-$N$ into the level-$Nq$ function field over $\overline{\mathbb Q}$, a place specialisation $P$ of this data, a prolongation tuple $R$ over $P$, a finite set $W$ of places of `modularFunctionFieldC k N` over $k$, and a level-$N$ annulus datum `dat` for $R$ over $W$ (intermediate fields $K_w \subseteq \overline{\mathbb Q}$, node coordinates over $K_w$ at each $w \in W$, widths, a rational depth function $\delta$ on the places of `modularFunctionFieldBar (N * q)`, uniformisers, correction divisors and units in $k^{\times}$). Assume: every element $\sigma$ of the inertia subgroup of $A$ over $\mathbb Q$ fixes $K_w$ pointwise for all $w \in W$; for every $w \in W$ and every place $V$ of `modularFunctionFieldBar (N * q)` with $P.\mathrm{reduceFst}\,V = w$ which is neither strict for the first nor for the second reduction (the two conditions comparing $\mathrm{reduceFst}\,V$ and $\mathrm{reduceSnd}\,V$ through the Frobenius on places of the level-$N$ fibre), one has $0 < \delta(V) < \mathrm{width}(w)$ and $\mathrm{yDepth}(V)^{\mathrm{den}\,\delta(V)} = v_A(q)^{\mathrm{num}\,\delta(V)}$, where $\mathrm{yDepth}(V)$ is the $A$-valuation of the value at $V$ of the $y$-coordinate of the node coordinates at $w$; $\delta$ is invariant under the arithmetic Galois action of inertia on places. Let $E$ be a divisor on `modularFunctionFieldBar (N * q)` over $\overline{\mathbb Q}$ fixed by the arithmetic Galois action of every inertia element. Then for every $w \in W$ and every natural number $d$ the tent-weighted circle degree $\sum_V E(V)\max(0, 1 - |\delta(V) - d|)$ has denominator $1$, and the depth moment $\sum_V E(V)\delta(V)$ has denominator $1$, both sums running over the places $V$ in the support of $E$ with $P.\mathrm{reduceFst}\,V = w$ that are neither strict for the first nor for the second reduction.
--
--   This is the orbit-integrality statement for the depth invariants attached to an inertia-stable divisor on the level-$Nq$ modular curve: the piecewise-affine tent weights and the first depth moment, a priori rational, take integer values. It is used in the subsequent analysis of annulus data, where chords, end orders and coupled scalings of twists are extracted from such divisors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumLevel_den_circleDeg_eq_one_and_den_depthMoment_eq_one_of_inertiaStable.lean

import Mathlib
import Definitions.Def_ModularCurve_AnnulusSpecializationLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization
open Classical in

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumLevel.den_circleDeg_eq_one_and_den_depthMoment_eq_one_of_inertiaStable
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} {R : ProlongationTuple P}
    {W : Finset (Place k (modularFunctionFieldC k N))}
    (dat : R.AnnulusDatumLevel W)
    (hKfix : ∀ w ∈ W, ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ z ∈ dat.K w, σ z = z)
    (hdepthQ : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
        (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
        P.reduceFst V = w → ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V →
          0 < dat.depthQ V ∧ dat.depthQ V < dat.width w ∧ (dat.coord w hw).yDepth V ^ (dat.depthQ V).den =
            A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ^ (dat.depthQ V).num.toNat)
    (hdepthσ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
        dat.depthQ (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V) = dat.depthQ V)
    E
    (hEstab : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • E = E) :
    (∀ w ∈ W, ∀ d : ℕ, (dat.circleDeg E w d).den = 1) ∧ (∀ w ∈ W, (dat.depthMoment E w).den = 1) := by sorry
