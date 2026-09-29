-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_fixed_strict_add_kernelGood_of_isTwistOf_of_inertiaStable
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumQ.exists_fixed_strict_add_kernelGood_of_isTwistOf_of_inertiaStable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/4f643dd7-9b6c-5364-88ca-3d41c3c5a568
-- title:
--   Inertia-stable twisted divisor: fixed strict part plus glue-trivial part
-- statement:
--   Let $q\ge 5$ be a prime, $A$ a valuation subring of $\overline{\mathbf Q}$, $k$ an algebraically closed field of characteristic $q$ and $red:A\to k$ a ring homomorphism; let `data` be modular polynomial data for $q$ satisfying the Kronecker congruence, and assume the two Hecke correspondences at level $1$ and $q$ are integral. Let $P$ be a place specialisation at level $1$ for these data, and $W$ a finite set of places of $\mathrm{modularFunctionFieldC}\,k\,1$ consisting exactly of the supersingular places `ssPlaces q 1 k`. Let $R$ be a prolongation tuple for $P$ satisfying `IsModel` (the two divisor laws and the two cusp laws), the regularity law, the node-value law over $W$, and the fixed order law, and let `dat` be an orbit annulus datum for $R$ over $W$: coordinate fields $K(w)\subset\overline{\mathbf Q}$, node coordinates, integral widths, a rational depth function `depthQ` on places of $\mathrm{modularFunctionFieldBar}(1\cdot q)$, a cusp, uniformisers, and units $u_0,\lambda,\mu$ of $k$. The hypotheses on this datum, summarised here, fall into the groups: width laws ($1\le$ width, and width $=\mathrm{jWidth}$ of the value of the geometric $j$, i.e.\ $3,2,1$ according as that value is $0$, $1728$ or neither); depth laws (for $V$ with $P.\mathrm{reduceFst}\,V=w\in W$ and $V$ neither `IsStrictFst` nor `IsStrictSnd`, $0<\mathrm{depthQ}\,V<\mathrm{width}\,w$ and the cleared relation $\mathrm{yDepth}_V^{\,\mathrm{den}}=v_A(q)^{\mathrm{num}}$, together with invariance of `depthQ` under the arithmetic Galois action of the inertia subgroup of $A$ over $\mathbf Q$); cusp and uniformiser laws (the cusp lies outside $W$ and is fixed by `arithFrobC`, and the uniformisers have divisors $w-\mathrm{cusp}$ and $\mathrm{arithFrobC}\cdot w-\mathrm{cusp}$); coefficient laws (each $K(w)$ is finite over $\mathbf Q$ and fixed pointwise by inertia, $\varpi_w$ generates the kernel of reduction on the coefficient subring, $q=\varpi_w^{e_w}\varepsilon_w$ with $e_w\ge1$ and $\varepsilon_w$ a unit reducing to $1$); crossing laws at each $w\in W$ (the product of the two node coordinates is $\varpi_w^{\mathrm{width}\cdot e_w}$ times a unit, $(\varpi_w,x,y)$ is the unique maximal ideal, $(\varpi_w,x)$ and $(\varpi_w,y)$ are prime with $y$, resp.\ $x$, outside them, the ring of node integers is Noetherian, and every element differs from a constant by a non-unit); and value laws (value integrality at $w$, and the prescribed residues $u_0$, $\lambda$, $\mu$ of $u$, $y/\mathrm{unifFst}$, $x/\mathrm{unifSnd}$). Finally let $X$ be a degree-zero divisor on $\mathrm{modularFunctionFieldBar}(1\cdot q)$ over $\overline{\mathbf Q}$ that is invariant under the arithmetic Galois action of the inertia subgroup of $A$ over $\mathbf Q$ and whose support consists of places that are `IsStrictFst`, `IsStrictSnd`, or reduce under $P.\mathrm{reduceFst}$ into $W$, and let $a$ be a twist vector with $\mathrm{dat}.\mathrm{IsTwistOf}\,a\,X$ (the two end-order degree equations and the circle-degree equations of the orbit edition). The conclusion asserts the existence of degree-zero divisors $D_t$ and $D_2$ such that every place in the support of $D_t$ is fixed by the inertia action and is `IsStrictFst` or `IsStrictSnd`; $D_2$ is a good divisor for $P$, i.e.\ its support is strict; the gluing datum $P.\mathrm{glueData}$ of $D_2$ for the node pairs $(w,\mathrm{arithFrobC}\cdot w)$, $w\in W$, is admissible and its class in `GluedPic0` vanishes; and $X-D_t-D_2$ is principal.
--
--   This is the torus, or kernel, half of the kernel-reach step for inertia-stable degree-zero divisors whose glued component class vanishes: an inertia-stable divisor satisfying the twist equations is decomposed, modulo principal divisors, into a divisor supported on inertia-fixed strict places and a strict divisor with trivial glued Picard class. It is used by [`ModularCurve.PlaceSpecialization.exists_fixedStrict_kernelGood_principal`](thm.html#ModularCurve.PlaceSpecialization.exists_fixedStrict_kernelGood_principal).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_fixed_strict_add_kernelGood_of_isTwistOf_of_inertiaStable.lean

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

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumQ.exists_fixed_strict_add_kernelGood_of_isTwistOf_of_inertiaStable
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
    (X : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q)))))
    (hXstab : ∀ σ ∈ A.inertiaSubgroupIn ℚ,
        arithmeticGalois (modularFunctionFieldFull (1 * q)) σ •
          (X : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) = X)
    (hXsupp : ∀ V ∈ (X : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))).support,
        P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W)
    (a : ProlongationTuple.TwistVector (k := k) W)
    (ha : dat.IsTwistOf a (X : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))) :
    ∃ (Dt D₂ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q))))),
      (∀ V ∈ (Dt : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))).support,
        (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V = V) ∧
          (P.IsStrictFst V ∨ P.IsStrictSnd V)) ∧
      P.IsGoodDiv (D₂ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) ∧
      (∃ hadm : P.glueData (nodePairsOfPlaces (arithFrobC q k 1) W)
            (D₂ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
          ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k 1) W),
        GluedPic0.mk (nodePairsOfPlaces (arithFrobC q k 1) W)
          ⟨P.glueData (nodePairsOfPlaces (arithFrobC q k 1) W)
            (D₂ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))), hadm⟩ = 0) ∧
      ((X : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) - Dt - D₂) ∈
        Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q))) := by sorry
