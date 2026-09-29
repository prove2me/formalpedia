-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_fixed_strict_mk_glueData_eq
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumQ.exists_fixed_strict_mk_glueData_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/40a38952-91c6-5d11-b2ab-6c0bbb076efd
-- title:
--   Glued classes from inertia-fixed strict divisors with zero twist
-- statement:
--   Fix a prime $q \ge 5$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $\mathrm{red} : A \to k$, modular polynomial data `data` for $q$ satisfying the Kronecker congruence $\Phi \equiv (X^q - Y)(X - Y^q)$ modulo $q$, integrality of the two level-raising maps $\alpha, \beta$ from level $1$ to level $q$, and a place specialization $P$ for these data; let $W$ be a finite set of places of the geometric function field `modularFunctionFieldC` $k\,1$ whose members are exactly the supersingular places `ssPlaces q 1 k`, and $R$ a prolongation tuple over $P$ satisfying `IsModel`, the regularity and node-value laws for $W$, and the fixed order law. Let `dat` be an annulus datum of orbit type for $R$ and $W$: intermediate fields $K(w) \subset \overline{\mathbb{Q}}$, node coordinates $(x_w, y_w)$ over $K(w)$ for $w \in W$, widths $\mathrm{width}(w) \in \mathbb{N}$, a depth function $\mathrm{depthQ}$ on places of the level-$q$ field with values in $\mathbb{Q}$, a cusp place, uniformisers $\mathrm{unifFst}(w)$, $\mathrm{unifSnd}(w)$, and units $u_0(w), \lambda(w), \mu(w)$ of $k$. The hypotheses, summarised here in groups, are: $\mathrm{width}(w) \ge 1$ and $\mathrm{width}(w) = \mathrm{jWidth}(w(j))$ for $w \in W$, so the width is $3$, $2$ or $1$ according as the $j$-value is $0$, $1728$ or neither; for each $w \in W$ and each place $V$ of the level-$q$ field with $P.\mathrm{reduceFst}\,V = w$ that is neither strict-first nor strict-second, $0 < \mathrm{depthQ}(V) < \mathrm{width}(w)$ together with the relation $\mathrm{yDepth}(V)^{\mathrm{den}} = v_A(q)^{\mathrm{num}}$ for the coordinate $y_w$; invariance of $\mathrm{depthQ}$ under the arithmetic Galois action of the inertia subgroup of $A$ over $\mathbb{Q}$; the cusp lies outside $W$ and is fixed by the geometric arithmetic Frobenius `arithFrobC q k 1`; the divisors of $\mathrm{unifFst}(w)$ and $\mathrm{unifSnd}(w)$ are $w - \mathrm{cusp}$ and $\mathrm{Frob}(w) - \mathrm{cusp}$; each $K(w)$ is finite over $\mathbb{Q}$ and fixed pointwise by inertia; elements $\varpi(w)$ of the coefficient subring $A \cap K(w)$ generating the kernel of the induced reduction, exponents $e_K(w) \ge 1$ and units $\varepsilon(w)$ with residue $1$ such that $q = \varpi(w)^{e_K(w)} \varepsilon(w)$; units $u(w)$ of the node ring with $x_w y_w = \varpi(w)^{\mathrm{width}(w) e_K(w)} u(w)$; that $(\varpi(w), x_w, y_w)$ is the unique maximal ideal of the node ring, that $(\varpi(w), x_w)$ and $(\varpi(w), y_w)$ are prime with $y_w$ outside the first and $x_w$ outside the second, Noetherianity of the node rings, a residue condition that every element of the node ring differs from some constant by a non-unit, the value integrality law at $w$, and the normalisations $w(u(w)) = u_0(w)$, $w(y_w/\mathrm{unifFst}(w)) = \lambda(w)$, $\mathrm{Frob}(w)(x_w/\mathrm{unifSnd}(w)) = \mu(w)$ on the two residues. Then for every class $g$ in the glued degree-zero divisor class group `GluedPic0` attached to the node pairs $(w, \mathrm{Frob}(w))$, $w \in W$, there is a degree-zero divisor $D_t$ on the level-$q$ field over $\overline{\mathbb{Q}}$ such that every place in the support of $D_t$ is fixed by the arithmetic Galois action of every element of the inertia subgroup of $A$ over $\mathbb{Q}$ and is strict-first or strict-second for $P$, such that `dat.IsTwistOf` holds for $D_t$ with the zero twist vector $(0,0,0)$, such that $D_t$ is a good divisor for $P$, and such that the gluing datum $P.\mathrm{glueData}$ of $D_t$, namely the pair of pushforwards along $\mathrm{reduceFst}$ and $\mathrm{reduceSnd}$ of the strict-first and strict-second parts of $D_t$ with trivial unit component, is admissible and its class in `GluedPic0` equals $g$.
--
--   This is the surjectivity step for the specialization map onto the glued degree-zero class group of the two $j$-lines identified along the supersingular crossings: every glued class is reached by a divisor in characteristic zero whose points are inertia-fixed and strict for the two reduction maps, with both branch degrees zero. It feeds the kernel-reach assembly [`ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumQ.exists_fixed_strict_add_kernelGood_of_isTwistOf_of_inertiaStable`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumQ.exists_fixed_strict_add_kernelGood_of_isTwistOf_of_inertiaStable), which combines it with the computation of the toric part of the degeneration.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_fixed_strict_mk_glueData_eq.lean

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

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumQ.exists_fixed_strict_mk_glueData_eq
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
    (hdepthQ : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W)
        (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))),
        P.reduceFst V = w → ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V →
          0 < dat.depthQ V ∧ dat.depthQ V < dat.width w ∧ (dat.coord w hw).yDepth V ^ (dat.depthQ V).den =
            A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ^ (dat.depthQ V).num.toNat)
    (hdepthσ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
        dat.depthQ (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V) = dat.depthQ V)
    (hcusp : dat.cusp ∉ W) (hcuspφ : arithFrobC q k 1 • dat.cusp = dat.cusp)
    (hunif : ∀ w ∈ W,
      (∀ v : Place k (modularFunctionFieldC k 1),
          ((Finsupp.single w (1 : ℤ) - Finsupp.single dat.cusp 1 :
              Divisor k ↥(modularFunctionFieldC k 1)) v) = v.ord (dat.unifFst w)) ∧
      (∀ v : Place k (modularFunctionFieldC k 1),
          ((Finsupp.single (arithFrobC q k 1 • w) (1 : ℤ) - Finsupp.single dat.cusp 1 :
              Divisor k ↥(modularFunctionFieldC k 1)) v) = v.ord (dat.unifSnd w)))
    (hKfix : ∀ w ∈ W, ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ z ∈ dat.K w, σ z = z)
    [hK : ∀ w : Place k (modularFunctionFieldC k 1), FiniteDimensional ℚ ↥(dat.K w)]
    (ϖ : ∀ w : Place k (modularFunctionFieldC k 1), ↥(NodeLocalized.coeffSubring A (dat.K w)))
    (hϖ : ∀ w ∈ W, ∀ d : ↥(NodeLocalized.coeffSubring A (dat.K w)),
      NodeLocalized.redRestrict red (dat.K w) d = 0 ↔ ∃ d', d = ϖ w * d')
    (eK : Place k (modularFunctionFieldC k 1) → ℕ) (heK : ∀ w ∈ W, 1 ≤ eK w)
    (ε : ∀ w : Place k (modularFunctionFieldC k 1), ↥(NodeLocalized.coeffSubring A (dat.K w)))
    (hε : ∀ w ∈ W, IsUnit (ε w))
    (hqϖ : ∀ w ∈ W, ((q : ℕ) : ↥(NodeLocalized.coeffSubring A (dat.K w))) = ϖ w ^ eK w * ε w)
    (hε1 : ∀ w ∈ W, NodeLocalized.redRestrict red (dat.K w) (ε w) = 1)
    (u : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W), ↥(R.nodeIntegersOver (dat.K w) w))
    (hu : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W), IsUnit (u w hw) ∧
        (dat.coord w hw).x * (dat.coord w hw).y = R.nodeConst (dat.K w) w (ϖ w) ^ (dat.width w * eK w) * u w hw)
    (hmax : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W),
        (Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).x, (dat.coord w hw).y}).IsMaximal ∧
        ∀ M : Ideal ↥(R.nodeIntegersOver (dat.K w) w), M.IsMaximal →
          M = Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).x, (dat.coord w hw).y})
    (hbr : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W),
        (Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).x}).IsPrime ∧
        (Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).y}).IsPrime ∧
        (dat.coord w hw).y ∉ Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).x} ∧
        (dat.coord w hw).x ∉ Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).y})
    (hnoeth : ∀ w ∈ W, IsNoetherianRing ↥(R.nodeIntegersOver (dat.K w) w))
    (hres : ∀ w ∈ W, ∀ g : ↥(R.nodeIntegersOver (dat.K w) w),
        ∃ o : ↥(NodeLocalized.coeffSubring A (dat.K w)), ¬ IsUnit (g - R.nodeConst (dat.K w) w o))
    (hVI : ∀ w ∈ W, R.ValueIntegralityLaw w)
    (hu0 : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W),
      w.HasValue (R.nodeResidue₁ w ⟨(u w hw : ↥(modularFunctionFieldBar (1 * q))), (u w hw).2.1⟩) ((dat.u0 w : kˣ) : k))
    (hlam : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W),
      w.HasValue (R.nodeResidue₁ w ⟨((dat.coord w hw).y : ↥(modularFunctionFieldBar (1 * q))), (dat.coord w hw).y.2.1⟩
        / dat.unifFst w) ((dat.lam w : kˣ) : k))
    (hmu : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W),
      (arithFrobC q k 1 • w).HasValue
        (R.nodeResidue₂ w ⟨((dat.coord w hw).x : ↥(modularFunctionFieldBar (1 * q))), (dat.coord w hw).x.2.1⟩
          / dat.unifSnd w) ((dat.mu w : kˣ) : k))
    (g : GluedPic0 k (modularFunctionFieldC k 1) (nodePairsOfPlaces (arithFrobC q k 1) W)) :
    ∃ Dt : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q)))),
      (∀ V ∈ (Dt : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))).support,
        (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V = V) ∧
          (P.IsStrictFst V ∨ P.IsStrictSnd V)) ∧
      dat.IsTwistOf ⟨0, 0, fun _ _ => 0⟩ (Dt : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) ∧
      P.IsGoodDiv (Dt : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) ∧
      ∃ hadm : P.glueData (nodePairsOfPlaces (arithFrobC q k 1) W) (Dt : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k 1) W),
        GluedPic0.mk (nodePairsOfPlaces (arithFrobC q k 1) W) ⟨P.glueData (nodePairsOfPlaces (arithFrobC q k 1) W) (Dt : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))), hadm⟩ = g := by sorry
