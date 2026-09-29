-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumQ.exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/f87bb64e-2429-50e6-94fa-dd48a1422060
-- title:
--   Strict representative of an inertia-stable, glued-trivial divisor class
-- statement:
--   Fix a prime $q \ge 5$, a valuation subring $A$ of $\overline{\mathbf Q}$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $red : A \to k$, modular polynomial data `data` for $q$ satisfying the Kronecker congruence, integrality of the two degeneracy embeddings at level $1$, and a place specialisation $P$ of $A$ at $q$ and level $1$ relative to these. Let $W$ be the finite set of places of $\mathrm{modularFunctionFieldC}\,k\,1$ consisting exactly of the supersingular places `ssPlaces q 1 k`, let $R$ be a prolongation tuple for $P$ satisfying `IsModel`, `RegularityLaw W`, `NodeValueLaw W` and `OrderLawFixed`, and let `dat` be an orbit annulus datum for $R$ over $W$. The datum is assumed to satisfy: each width is at least $1$ and equals $\mathrm{jWidth}$ of the value of the geometric $j$-generator at $w$; for every $w \in W$ and every place $V$ of $\mathrm{modularFunctionFieldBar}(1\cdot q)$ reducing to $w$ under `reduceFst` that is neither strict on the first nor on the second side, the rational depth `depthQ V` lies strictly between $0$ and the width of $w$ and its cleared form matches the $y$-depth of the node coordinates against the $A$-valuation of $q$; `depthQ` is invariant under the arithmetic Galois action of the inertia subgroup of $A$ over $\mathbf Q$; the cusp place lies outside $W$ and is fixed by the geometric arithmetic Frobenius `arithFrobC q k 1`; for $w \in W$ the elements `unifFst w`, `unifSnd w` have divisors $w - \mathrm{cusp}$ and $\mathrm{Frob}(w) - \mathrm{cusp}$; each coefficient field `dat.K w` is finite-dimensional over $\mathbf Q$ and fixed pointwise by inertia. Further data are given: elements $\varpi w$ of the coefficient subring $A \cap \mathrm{dat.K}\,w$ generating the kernel of the reduction `redRestrict red (dat.K w)`, integers $eK\,w \ge 1$ and units $\varepsilon w$ reducing to $1$ with $q = \varpi w^{eK\,w}\,\varepsilon w$, and units $u\,w$ of the node integers over `dat.K w` at $w$ with $xy = \mathrm{nodeConst}(\varpi w)^{\,\mathrm{width}(w)\cdot eK(w)} u\,w$ for the node coordinates $x,y$; the ideal spanned by $\mathrm{nodeConst}(\varpi w), x, y$ is maximal and is the only maximal ideal, the two branch ideals spanned by $\mathrm{nodeConst}(\varpi w)$ together with $x$, resp. $y$, are prime with $y$, resp. $x$, outside them, the ring is Noetherian, and no element of it becomes a unit after subtracting a suitable constant; the value-integrality law holds at each $w \in W$; and the residues of $u\,w$, of $y/\mathrm{unifFst}\,w$ and of $x/\mathrm{unifSnd}\,w$ take the prescribed values $u_0(w)$, $\lambda(w)$, $\mu(w)$ in $k^\times$ at $w$, $w$ and $\mathrm{Frob}(w)$ respectively. Finally, let $X$ be a degree-zero divisor on $\mathrm{modularFunctionFieldBar}(1\cdot q)$ that is invariant under the arithmetic Galois action of inertia, each place of whose support is strict on the first side, strict on the second side, or reduces under `reduceFst` into $W$, let $a$ be a twist vector for $W$ with `dat.IsTwistOf a X`, and suppose the gluing datum `dat.spData a X` is admissible for the node pairing $\{(w, \mathrm{Frob}\,w) : w \in W\}$ and has trivial class in the glued degree-zero Picard group. Then there exists a degree-zero divisor $D_2$ on $\mathrm{modularFunctionFieldBar}(1\cdot q)$ whose canonical gluing datum $P.\mathrm{glueData}$ (the pushforwards of its first and second parts along `reduceFst` and `reduceSnd`, with trivial unit component) is admissible, such that every place in the support of $D_2$ is strict on one of the two sides, the class of that gluing datum in the glued degree-zero Picard group is zero, and $D_2$ and $X$ define the same class in $\mathrm{Pic}^0$.
--
--   This is the representative-moving step in the analysis of the kernel of specialisation on degree-zero classes at level one: a divisor class whose twisted gluing datum is glued-trivial is rewritten, without changing its $\mathrm{Pic}^0$ class, by a divisor supported only at places strict for one of the two reductions, with glued-trivial canonical gluing datum. The support hypothesis is stability of the divisor under inertia rather than pointwise fixedness of its support, and the result feeds the decomposition of inertia-stable classes into a fixed strict part and a good kernel part.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.lean

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

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumQ.exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable
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
        arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • (X : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) = X)
    (hXsupp : ∀ V ∈ (X : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))).support, P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W)
    (a : ProlongationTuple.TwistVector (k := k) W)
    (ha : dat.IsTwistOf a (X : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))))
    (hadm : dat.spData a (X : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k 1) W))
    (hsp : GluedPic0.mk (nodePairsOfPlaces (arithFrobC q k 1) W) ⟨dat.spData a (X : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))), hadm⟩ = 0) :
    ∃ (D₂ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q)))))
      (hadm₂ : P.glueData (nodePairsOfPlaces (arithFrobC q k 1) W) (D₂ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k 1) W)),
      P.IsGoodDiv (D₂ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) ∧
      GluedPic0.mk (nodePairsOfPlaces (arithFrobC q k 1) W) ⟨P.glueData (nodePairsOfPlaces (arithFrobC q k 1) W) (D₂ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))), hadm₂⟩ = 0 ∧
      Pic0.mk D₂ = Pic0.mk X := by sorry
