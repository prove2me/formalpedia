-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_chord_le_endOrders_and_rigid_of_isTwistOf_of_inertiaStable
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumQ.exists_chord_le_endOrders_and_rigid_of_isTwistOf_of_inertiaStable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/b00a7d60-44c2-54b7-bf66-02db18223cfb
-- title:
--   Chord bound, rigidity and scaling increment for twisted annulus data
-- statement:
--   Fix a prime $q$ with $5 \le q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$ (an algebraic closure of $\mathbb{Q}$), an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$, together with modular polynomial data $data$ for $q$ and a proof $hKr$ that it satisfies the Kronecker congruence $\Phi \equiv (Y^q - X)(Y - X^q)$ modulo $q$, and integrality hypotheses $h\alpha$, $h\beta$ for the two Hecke degeneracy maps $\mathrm{heckeAlphaBar}$, $\mathrm{heckeBetaBar}$ at level $1$ and prime $q$. Let $P$ be a `PlaceSpecialization` for these data, let $W$ be a finite set of places of the characteristic-$q$ modular function field `modularFunctionFieldC k 1` with $hW$ asserting that membership in $W$ is equivalent to membership in `ssPlaces q 1 k`, the set of supersingular places, and let $R$ be a `ProlongationTuple` for $P$, carrying two regular prolongations $R.R_1$, $R.R_2$ of $A$ to `modularFunctionFieldBar (1 * q)` with residue maps into the geometric special fibre. The hypothesis $hR$ states that $R$ is a model, i.e. satisfies the two divisor laws and the two cusp laws; $hRL$ is the regularity law for $W$, $hNV$ the node value law for $W$, and $hO$ the fixed-place order law, which computes the push-forward along `P.reduceFst` of the divisor of a function whose two residues are non-zero as the sum of the order of the first residue at $v$ and the order of the second residue at the Frobenius image of $v$, for Frobenius-fixed affine geometric places $v$. Finally $hker$ says that $red$ has kernel exactly the maximal ideal of $A$.
--
--   Let $dat$ be an `AnnulusDatumQ` for $R$ and $W$: it assigns to each place $w$ an intermediate field $dat.K\,w$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, to each $w \in W$ node coordinates $dat.\mathrm{coord}\,w$, a width $dat.\mathrm{width}\,w \in \mathbb{N}$, a rational depth $dat.\mathrm{depthQ}\,V$ for each place $V$ of `modularFunctionFieldBar (1 * q)`, a distinguished place $dat.\mathrm{cusp}$, uniformisers $dat.\mathrm{unifFst}\,w$, $dat.\mathrm{unifSnd}\,w$ and units $dat.u_0\,w$, $dat.\mathrm{lam}\,w$, $dat.\mathrm{mu}\,w$ of $k$.
--
--   The hypotheses on this datum are as follows. Widths: $hwidth$ requires $1 \le dat.\mathrm{width}\,w$ for $w \in W$, and $hwidthj$ requires $dat.\mathrm{width}\,w = \mathrm{jWidth}(w.\mathrm{evalAt}(\mathrm{jGeomGen}\,k\,1))$, that is $3$, $2$ or $1$ according as the value of the $j$-generator at $w$ is $0$, $1728$ or neither. Depths: $hdepthQ$ requires, for $w \in W$ and every place $V$ with $P.\mathrm{reduceFst}\,V = w$ which is neither strictly first nor strictly second for $P$, that $0 < dat.\mathrm{depthQ}\,V < dat.\mathrm{width}\,w$ and that the $y$-depth $A.\mathrm{valuation}(V.\mathrm{evalAt}\,y)$ of the node coordinate $y$ at $V$, raised to the denominator of $dat.\mathrm{depthQ}\,V$, equals $A.\mathrm{valuation}(q)$ raised to its numerator; $hdepth\sigma$ requires $dat.\mathrm{depthQ}$ to be invariant under the action of the inertia subgroup $A.\mathrm{inertiaSubgroupIn}\,\mathbb{Q}$ on places through $\mathrm{arithmeticGalois}$. Cusp and uniformisers: $hcusp$ requires $dat.\mathrm{cusp} \notin W$ and $hcusp\varphi$ that it is fixed by $\mathrm{arithFrobC}\,q\,k\,1$; $hunif$ requires, for each $w \in W$, that the divisor of $dat.\mathrm{unifFst}\,w$ be $(w) - (dat.\mathrm{cusp})$ and the divisor of $dat.\mathrm{unifSnd}\,w$ be $(\mathrm{arithFrobC}\,q\,k\,1 \cdot w) - (dat.\mathrm{cusp})$.
--
--   Coefficient rings at the nodes: $hKfix$ requires each element of $dat.K\,w$, for $w \in W$, to be fixed by every element of the inertia subgroup, and each $dat.K\,w$ is assumed finite-dimensional over $\mathbb{Q}$. For each place there is given an element $\varpi\,w$ of the coefficient subring $A \cap dat.K\,w$, and $h\varpi$ requires, for $w \in W$, that an element of this subring reduce to $0$ under $\mathrm{redRestrict}\,red$ precisely when it is a multiple of $\varpi\,w$; further data $eK\,w \in \mathbb{N}$ with $1 \le eK\,w$ on $W$ ($heK$), elements $\varepsilon\,w$ of the same subring which are units on $W$ ($h\varepsilon$), satisfy $q = (\varpi\,w)^{eK\,w}\,\varepsilon\,w$ there ($hq\varpi$) and reduce to $1$ ($h\varepsilon 1$).
--
--   Node equations: for $w \in W$ an element $u\,w$ of the node ring $R.\mathrm{nodeIntegersOver}(dat.K\,w)\,w$ is given, and $hu$ requires it to be a unit with $x \cdot y = (\mathrm{nodeConst}(\varpi\,w))^{\,dat.\mathrm{width}\,w \cdot eK\,w} \cdot u\,w$ for the node coordinates $x, y$ of $dat.\mathrm{coord}\,w$; $hmax$ requires the ideal spanned by $\mathrm{nodeConst}(\varpi\,w)$, $x$, $y$ to be maximal and to be the only maximal ideal of that ring; $hbr$ requires the ideals spanned by $\{\mathrm{nodeConst}(\varpi\,w), x\}$ and by $\{\mathrm{nodeConst}(\varpi\,w), y\}$ to be prime with $y$ outside the first and $x$ outside the second; $hnoeth$ requires the node ring to be Noetherian; $hres$ requires every element $g$ of it to differ from some constant $\mathrm{nodeConst}\,o$ by a non-unit; $hVI$ requires the value integrality law at each $w \in W$, namely that for $f$ in $R.\mathrm{nodeIntegers}\,w$ and every $V$ with $P.\mathrm{reduceFst}\,V = w$ the value $V.\mathrm{evalAt}\,f$ lies in $A$.
--
--   Node values: $hu0$ requires the first-sheet node residue of $u\,w$ to have value $dat.u_0\,w$ at $w$; $hlam$ requires the first-sheet node residue of $y$ divided by $dat.\mathrm{unifFst}\,w$ to have value $dat.\mathrm{lam}\,w$ at $w$; $hmu$ requires the second-sheet node residue of $x$ divided by $dat.\mathrm{unifSnd}\,w$ to have value $dat.\mathrm{mu}\,w$ at $\mathrm{arithFrobC}\,q\,k\,1 \cdot w$.
--
--   The twisted divisor: $D$ is a degree-zero divisor on `modularFunctionFieldBar (1 * q)`, stable under the inertia subgroup ($hDstab$) and with every place of its support either strictly first, or strictly second, or reducing under $P.\mathrm{reduceFst}$ into $W$ ($hDsupp$). A twist vector $a$ (integers $a.aZ$, $a.aZ'$ and a family $a.aE$) is given with $ha : dat.\mathrm{IsTwistOf}\,a\,D$, i.e. the degree of the strictly-first part of $D$ is $-\sum_{w \in W} dat.\mathrm{endOrderFst}\,a\,D\,w$, the degree of its strictly-second part is $-\sum_{w \in W} dat.\mathrm{endOrderSnd}\,a\,D\,w$, and for $w \in W$ and $1 \le d$ with $d + 1 \le dat.\mathrm{width}\,w$ the circle degree $dat.\mathrm{circleDeg}\,D\,w\,d$ equals minus the second difference of $dat.\mathrm{chainVal}\,a\,w$ at $d$; here $\mathrm{endOrderFst}$ and $\mathrm{endOrderSnd}$ are the sums of the end slopes of $a$ and the end shares of $D$. Moreover $hadm$ requires the gluing datum $dat.\mathrm{spData}\,a\,D$ — the pair of push-forwards of the strictly-first and strictly-second parts of $D$ along $P.\mathrm{reduceFst}$ and $P.\mathrm{reduceSnd}$, each corrected by a multiple of $(dat.\mathrm{cusp})$ so as to have degree zero, together with the node units $dat.\mathrm{nodeUnitOf}\,a\,D$ — to be admissible for the node pairs $\mathrm{nodePairsOfPlaces}(\mathrm{arithFrobC}\,q\,k\,1)\,W$, and $hsp$ requires its class in `GluedPic0` of those node pairs to vanish.
--
--   The function: finitely many places $Q_1 : \mathrm{Fin}\,d_1 \to \ldots$ and $Q_2 : \mathrm{Fin}\,d_2 \to \ldots$ are given, all strictly first for $P$ ($hQ_1$) respectively strictly second ($hQ_2$), together with an effective divisor $E \ge 0$ ($hE0$) and a non-zero $f$ in `modularFunctionFieldBar (1 * q)` ($hf0$) whose divisor is $E - \sum_i (Q_1 i) - \sum_j (Q_2 j) - D$, in the pointwise form $hdivf$.
--
--   Under these hypotheses there exists a rational number $\delta$ with the following four properties.
--
--   First, for every $c \in \overline{\mathbb{Q}}$ such that $c \cdot f$ lies in the integers of $R.R_1$ and has non-zero first residue, and every $w \in W$,
--   $$\delta \le dat.\mathrm{width}\,w \cdot \bigl(\mathrm{ord}_w(R.\mathrm{residue}_1(c \cdot f)) + dat.\mathrm{endOrderFst}\,a\,D\,w\bigr).$$
--
--   Second, for every $c \in \overline{\mathbb{Q}}$ such that $c \cdot f$ lies in the integers of $R.R_2$ and has non-zero second residue, and every $w \in W$,
--   $$-\,dat.\mathrm{width}\,w \cdot \bigl(\mathrm{ord}_{\mathrm{arithFrobC}\,q\,k\,1 \cdot w}(R.\mathrm{residue}_2(c \cdot f)) + dat.\mathrm{endOrderSnd}\,a\,D\,w\bigr) \le \delta.$$
--
--   Third, rigidity: if $\delta = 0$ then for all $c_1, c_2 \in \overline{\mathbb{Q}}$ with $c_1 \cdot f$ in the integers of $R.R_1$ and $c_2 \cdot f$ in the integers of $R.R_2$, both residues non-zero, and every $w \in W$, the vanishing of $\mathrm{ord}_{\mathrm{arithFrobC}\,q\,k\,1 \cdot w}(R.\mathrm{residue}_2(c_2 \cdot f)) + dat.\mathrm{endOrderSnd}\,a\,D\,w$ implies both that $\mathrm{ord}_w(R.\mathrm{residue}_1(c_1 \cdot f)) + dat.\mathrm{endOrderFst}\,a\,D\,w = 0$ and that $E\,V = 0$ for every place $V$ with $P.\mathrm{reduceFst}\,V = w$.
--
--   Fourth, the increment criterion: $\delta = 0$ holds if and only if, for every $c_1 \in \overline{\mathbb{Q}}$ such that $c_1 \cdot f$ lies in the integers of $R.R_1$ with non-zero first residue, the scaling $(c_1 \cdot q^{\,a.aZ' - a.aZ}) \cdot f$ lies in the integers of $R.R_2$ and has non-zero second residue.
--
--   This is the chord estimate for the twisted Gauss profile of a rational function along the supersingular annuli in the semistable reduction of $X_0(q)$ at $q$, in the version where the annulus datum records rational, inertia-invariant depths and the divisor $D$ is only assumed inertia-stable: it bounds the profile of $f$ between the two end orders at each supersingular place, records the rigid case, and identifies the jump between admissible scalings on the two sheets as a power of $q$ given by the twist vector. It is used in the companion result that adds the coupled node values of the two residues to the chord, rigidity and increment conclusions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_chord_le_endOrders_and_rigid_of_isTwistOf_of_inertiaStable.lean

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

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumQ.exists_chord_le_endOrders_and_rigid_of_isTwistOf_of_inertiaStable
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
    (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q)))))
    (hDstab : ∀ σ ∈ A.inertiaSubgroupIn ℚ,
        arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) = D)
    (hDsupp : ∀ V ∈ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))).support,
      P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W)
    (a : ProlongationTuple.TwistVector (k := k) W)
    (ha : dat.IsTwistOf a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))))
    (hadm : dat.spData a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
      ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k 1) W))
    (hsp : GluedPic0.mk (nodePairsOfPlaces (arithFrobC q k 1) W)
      ⟨dat.spData a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))), hadm⟩ = 0)

    {d₁ d₂ : ℕ}
    (Q₁ : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (Q₂ : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hQ₁ : ∀ i, P.IsStrictFst (Q₁ i)) (hQ₂ : ∀ j, P.IsStrictSnd (Q₂ j))
    (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hE0 : 0 ≤ E)
    (f : ↥(modularFunctionFieldBar (1 * q))) (hf0 : f ≠ 0)
    (hdivf : ∀ V, (E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ))
      - (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))) V = V.ord f)

    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    :
    ∃ δ : ℚ,

      (∀ (c : AlgebraicClosure ℚ) (h : c • f ∈ R.R₁.integers), R.R₁.residue ⟨c • f, h⟩ ≠ 0 →
        ∀ w ∈ W, δ ≤ (dat.width w : ℚ) * ((w.ord (R.residue₁ ⟨c • f, h⟩) : ℚ) + (dat.endOrderFst a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w : ℚ))) ∧

      (∀ (c : AlgebraicClosure ℚ) (h : c • f ∈ R.R₂.integers), R.R₂.residue ⟨c • f, h⟩ ≠ 0 →
        ∀ w ∈ W, -((dat.width w : ℚ) * (((arithFrobC q k 1 • w).ord (R.residue₂ ⟨c • f, h⟩) : ℚ)
          + (dat.endOrderSnd a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w : ℚ))) ≤ δ) ∧

      (δ = 0 → ∀ (c₁ : AlgebraicClosure ℚ) (h₁ : c₁ • f ∈ R.R₁.integers) (c₂ : AlgebraicClosure ℚ) (h₂ : c₂ • f ∈ R.R₂.integers),
        R.R₁.residue ⟨c₁ • f, h₁⟩ ≠ 0 → R.R₂.residue ⟨c₂ • f, h₂⟩ ≠ 0 →
        ∀ w ∈ W, (arithFrobC q k 1 • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩) + dat.endOrderSnd a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w = 0 →
          w.ord (R.residue₁ ⟨c₁ • f, h₁⟩) + dat.endOrderFst a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w = 0 ∧
          ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), P.reduceFst V = w → E V = 0) ∧

      (δ = 0 ↔ ∀ (c₁ : AlgebraicClosure ℚ) (h₁ : c₁ • f ∈ R.R₁.integers), R.R₁.residue ⟨c₁ • f, h₁⟩ ≠ 0 →
        ∃ h₂ : (c₁ * (q : AlgebraicClosure ℚ) ^ (a.aZ' - a.aZ)) • f ∈ R.R₂.integers,
          R.R₂.residue ⟨(c₁ * (q : AlgebraicClosure ℚ) ^ (a.aZ' - a.aZ)) • f, h₂⟩ ≠ 0) := by sorry
