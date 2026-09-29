-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_isTwistOf_sub_and_spData_sub_eq_of_forall_isStrict
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumQ.isTwistOf_sub_and_spData_sub_eq_of_forall_isStrict
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/82d8aed5-7a26-531d-b56d-c00496b8392c
-- title:
--   Subtracting a strict twist-zero divisor preserves the twist
-- statement:
--   Fix a prime $q$ with $5 \le q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $red : A \to k$, modular polynomial data `data` for $q$ satisfying the Kronecker congruence $hKr$, integrality of the two degeneracy maps $\overline{\alpha},\overline{\beta}$ from level $1$ to level $1\cdot q$, and a place specialisation $P$ for these data. Let $W$ be a finite set of places of the geometric level-$1$ modular function field $\mathrm{modularFunctionFieldC}\,k\,1$ whose members are exactly the supersingular places `ssPlaces q 1 k`, let $R$ be a prolongation tuple for $P$ satisfying `IsModel` (the two divisor laws and the two cusp laws), the regularity and node-value laws for $W$, and `OrderLawFixed`, and let `dat` be an annulus datum of orbit type for $R$ and $W$: intermediate fields $K(w) \subseteq \overline{\mathbb{Q}}$, node coordinates $\mathrm{coord}\,w$ for $w \in W$, widths $\mathrm{width}\,w$, a rational depth function $\mathrm{depthQ}$ on places of $\mathrm{modularFunctionFieldBar}(1\cdot q)$, a cusp place, uniformisers $\mathrm{unifFst},\mathrm{unifSnd}$, and units $u_0,\lambda,\mu \in k^\times$. A long list of normalisation hypotheses on `dat` is assumed, summarised here as: widths are at least $1$ and equal $\mathrm{jWidth}$ of the $j$-value at $w$ (namely $3$, $2$ or $1$ according as $j = 0$, $j = 1728$ or otherwise); the depths of non-strict places lie strictly between $0$ and the width and compute the $y$-valuation of the node coordinate as a power of the valuation of $q$; $\mathrm{depthQ}$ is invariant under the inertia subgroup of $A$ over $\mathbb{Q}$ acting through `arithmeticGalois`; the cusp lies outside $W$ and is fixed by the arithmetic Frobenius `arithFrobC q k 1`; $\mathrm{unifFst}\,w$ and $\mathrm{unifSnd}\,w$ have divisors $(w) - (\mathrm{cusp})$ and $(\mathrm{arithFrobC}\,q\,k\,1 \cdot w) - (\mathrm{cusp})$; inertia fixes $K(w)$ pointwise and $K(w)$ is finite over $\mathbb{Q}$; elements $\varpi\,w$ generating the kernel of the reduction of the coefficient subring of $A$ in $K(w)$, exponents $e_K(w) \ge 1$ and units $\varepsilon\,w$ reducing to $1$ with $q = \varpi\,w^{e_K(w)} \varepsilon\,w$; a unit $u$ with $x \cdot y = \mathrm{nodeConst}(\varpi\,w)^{\mathrm{width}(w) e_K(w)} u$ in the node integers over $K(w)$ at $w$; the span of $\{\varpi\,w, x, y\}$ being the unique maximal ideal, the two branch spans being prime with $y$ and $x$ not in the respective other span; Noetherianness, a non-unit condition for translates by constants, the value integrality law at $w$; and residue normalisations giving $u$, $y/\mathrm{unifFst}\,w$ and $x/\mathrm{unifSnd}\,w$ the values $u_0(w)$, $\lambda(w)$, $\mu(w)$. Finally let $X$ and $D_t$ be divisors on $\mathrm{modularFunctionFieldBar}(1\cdot q)$ with every place in the support of $D_t$ strict of first or second kind for $P$, let $a = (a_Z,a_Z',a_E)$ be a twist vector for $W$, and assume $X$ is a twist of $a$ and $D_t$ is a twist of the zero twist vector $(0,0,0)$, in the sense that the degree of the strict-first part equals minus the sum of the end orders of the first kind over $W$, likewise for the strict-second part, and each circle degree at admissible depth equals minus the second difference of the chain values. Then $X - D_t$ is again a twist of $a$, and the associated gluing datum satisfies $\mathrm{spData}\,a\,(X - D_t) = \mathrm{spData}\,a\,X - P.\mathrm{glueData}\,(\mathrm{nodePairsOfPlaces}\,(\mathrm{arithFrobC}\,q\,k\,1)\,W)\,D_t$, where the subtracted term has as its two divisor components the pushforwards along $\mathrm{reduceFst}$ and $\mathrm{reduceSnd}$ of the strict-first and strict-second parts of $D_t$ and has trivial unit component.
--
--   This is a bookkeeping step in the analysis of twisted gluing data attached to the annulus structure of the special fibre at $q$: a divisor supported at strict places and carrying the zero twist vector may be subtracted from a twist of $a$ without changing the twist vector, and its effect on the gluing datum is exactly the untwisted gluing datum of that divisor. It is used in the construction of inertia-fixed strict divisors in the kernel-reach argument, namely by [`ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumQ.exists_fixed_strict_add_kernelGood_of_isTwistOf_of_inertiaStable`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumQ.exists_fixed_strict_add_kernelGood_of_isTwistOf_of_inertiaStable).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_isTwistOf_sub_and_spData_sub_eq_of_forall_isStrict.lean

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

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumQ.isTwistOf_sub_and_spData_sub_eq_of_forall_isStrict
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
    (X Dt : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (hDt : ∀ V ∈ Dt.support, P.IsStrictFst V ∨ P.IsStrictSnd V)
    (a : ProlongationTuple.TwistVector (k := k) W)
    (ha : dat.IsTwistOf a X) (hz : dat.IsTwistOf ⟨0, 0, fun _ _ => 0⟩ Dt) :
    dat.IsTwistOf a (X - Dt) ∧
      dat.spData a (X - Dt) = dat.spData a X - P.glueData (nodePairsOfPlaces (arithFrobC q k 1) W) Dt := by sorry
