-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumLevel_exists_fixedGood_isTwistOf_sub_of_inertiaStable
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumLevel.exists_fixedGood_isTwistOf_sub_of_inertiaStable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/8b0ef32c-056d-585a-8c08-a516beadf535
-- title:
--   Inertia-fixed correction making a stable divisor twistable
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, an integer $N \ge 1$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $red : A \to k$, modular polynomial data `data` for $q$ satisfying the Kronecker congruence `hKr`, and integrality of the two degeneracy embeddings $\bar\alpha, \bar\beta$ of the Laurent base change of the full level-$N$ modular function field into that of level $Nq$; let $P$ be a place specialisation `PlaceSpecialization A q N data hKr k red hα hβ`, and assume $q \nmid N$. Let $W$ be a finite set of places of `modularFunctionFieldC k N` whose members are exactly the supersingular places, i.e. the rational affine geometric places $w$ whose value of the geometric $j$-generator lies in the supersingular $j$-set for $q$. Let $R$ be a prolongation tuple for $P$ and `dat` an annulus datum of level $W$ for $R$, consisting of intermediate fields $K_w \subseteq \overline{\mathbb{Q}}$, node coordinates over $K_w$ at each $w \in W$, widths $e_w \in \mathbb{N}$, a rational depth function $\delta$ on the places of the level-$Nq$ base-changed field, uniformisers, correction divisors and units. Assume: $e_w \ge 1$ for all $w \in W$; for every $w \in W$ and every place $V$ of the level-$Nq$ field with $\mathrm{red}_1 V = w$ which is neither strict of the first kind (`IsStrictFst`: the geometric-level Frobenius sends $\mathrm{red}_1 V$ to $\mathrm{red}_2 V$, and its square does not fix $\mathrm{red}_1 V$) nor strict of the second kind (`IsStrictSnd`, the mirror condition), one has $0 < \delta(V) < e_w$ and the cleared depth law $y\text{-}\mathrm{depth}(V)^{\mathrm{den}\,\delta(V)} = v_A(q)^{\mathrm{num}\,\delta(V)}$; $\delta$ is invariant under the action, through `arithmeticGalois`, of the inertia subgroup $I =$ `A.inertiaSubgroupIn ℚ` on places; for each $w \in W$ with $e_w \ge 2$ there is a place $V$ over $w$, neither strict of the first nor of the second kind, fixed by all of $I$, with $\delta(V) = 1$; and each $K_w$ is fixed pointwise by $I$. Let $E$ be a divisor of degree zero on the level-$Nq$ field over $\overline{\mathbb{Q}}$ that is $I$-stable and whose support consists of places that are strict of the first kind, strict of the second kind, or reduce under $\mathrm{red}_1$ into $W$, and let $B$ be any finite set of places of `modularFunctionFieldC k N`. Then there exists a divisor $D_{\mathrm{fix}}$ of degree zero such that every place $V$ in its support is fixed by all of $I$ and satisfies one of: $V$ is strict of the first kind with $\mathrm{red}_1 V \notin B$; $V$ is strict of the second kind with $\mathrm{red}_2 V \notin B$; or $\mathrm{red}_1 V \in W$, $V$ is neither strict of the first nor of the second kind, and $\delta(V) = 1$; and there exists a twist vector $a$ of level $W$ (two integers $a_Z, a_{Z'}$ and integers $a_E(w,d)$) with `dat.IsTwistOf a (E - Dfix)`, that is: the degree of the strict-first part of $E - D_{\mathrm{fix}}$ equals $-\sum_{w \in W} \mathrm{endOrderFst}(a, E - D_{\mathrm{fix}}, w)$, the same for the strict-second part with `endOrderSnd`, and for every $w \in W$ and every $d$ with $1 \le d$ and $d+1 \le e_w$ the circle degree $\mathrm{circleDeg}(E - D_{\mathrm{fix}}, w, d)$ equals minus the second difference $c(w,d-1) - 2c(w,d) + c(w,d+1)$ of the chain values of $a$.
--
--   This is the component-group step in the analysis of the special fibre at $q$ of the Néron model of $J_0(Nq)$ in the level-$N$ setting: the chain picture attached to the supersingular crossings (two vertices joined, for each $w \in W$, by a chain of length $e_w$) allows any inertia-stable degree-zero divisor to be corrected by inertia-fixed strict places and inertia-fixed annulus places of depth one until it satisfies the twist equations, i.e. lies in the identity component. It is used by [`ModularCurve.PlaceSpecialization.exists_inertiaFixedSupport_degZero_pic0Mk_eq_of_isModel`](thm.html#ModularCurve.PlaceSpecialization.exists_inertiaFixedSupport_degZero_pic0Mk_eq_of_isModel), and its proof combines the strict-place production theorem `exists_families_isStrictFst_isStrictSnd_notMem_forall_inertia_smul_eq`, the integrality statement `den_circleDeg_eq_one_and_den_depthMoment_eq_one_of_inertiaStable`, and the discrete Dirichlet-problem lemma `ChainDirichlet.exists_depthOne_correction_dirichlet`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumLevel_exists_fixedGood_isTwistOf_sub_of_inertiaStable.lean

import Mathlib
import Definitions.Def_ModularCurve_AnnulusSpecializationLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumLevel.exists_fixedGood_isTwistOf_sub_of_inertiaStable
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
    {W : Finset (Place k (modularFunctionFieldC k N))}
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P)
    (dat : R.AnnulusDatumLevel W)
    (hwidth : ∀ w ∈ W, 1 ≤ dat.width w)
    (hdepthQ : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
        (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
        P.reduceFst V = w → ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V →
          0 < dat.depthQ V ∧ dat.depthQ V < dat.width w ∧ (dat.coord w hw).yDepth V ^ (dat.depthQ V).den =
            A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ^ (dat.depthQ V).num.toNat)
    (hdepthσ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
        dat.depthQ (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V) = dat.depthQ V)
    (hD1 : ∀ w ∈ W, 2 ≤ dat.width w →
        ∃ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
          P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V ∧
          (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V) ∧
          dat.depthQ V = 1)
    (hKfix : ∀ w ∈ W, ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ z ∈ dat.K w, σ z = z)
    (E : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))))
    (hEstab : ∀ σ ∈ A.inertiaSubgroupIn ℚ,
        arithmeticGalois (modularFunctionFieldFull (N * q)) σ •
          (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) = E)
    (hEsupp : ∀ V ∈ (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).support,
        P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W)
    (B : Finset (Place k (modularFunctionFieldC k N))) :
    ∃ Dfix : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      Divisor.degree Dfix = 0 ∧
      (∀ V ∈ Dfix.support,
        (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V) ∧
        ((P.IsStrictFst V ∧ P.reduceFst V ∉ B) ∨ (P.IsStrictSnd V ∧ P.reduceSnd V ∉ B) ∨
          (P.reduceFst V ∈ W ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V ∧ dat.depthQ V = 1))) ∧
      ∃ a : ProlongationTuple.TwistVectorLevel (k := k) (N := N) W,
        dat.IsTwistOf a ((E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) - Dfix) := by sorry
