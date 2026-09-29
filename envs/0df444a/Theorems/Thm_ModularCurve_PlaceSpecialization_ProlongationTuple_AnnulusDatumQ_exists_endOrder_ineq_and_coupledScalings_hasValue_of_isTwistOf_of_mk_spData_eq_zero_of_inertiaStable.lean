-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_endOrder_ineq_and_coupledScalings_hasValue_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumQ.exists_endOrder_ineq_and_coupledScalings_hasValue_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/2148ab3b-01e5-52cd-b201-d244cb6b7bec
-- title:
--   End-order bounds and coupled scalings for an inertia-stable twist
-- statement:
--   Throughout, $q$ is a prime with $5 \le q$, $A$ is a valuation subring of $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ`, $k$ is an algebraically closed field of characteristic $q$, and $red : A \to k$ is a ring homomorphism. Further data: `data : ModularPolynomialData q`, that is a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$ of $q$-expansions, together with `hKr`, the Kronecker congruence $\Phi \equiv (X^q - Y)(X - Y^q) \bmod q$ in the form recorded by `KroneckerCongruence`; `hα` and `hβ`, the integrality of the two Hecke degeneracy maps `heckeAlphaBar` and `heckeBetaBar` from level $1$ to level $q$ over $\overline{\mathbb Q}$; and a place specialisation `P : PlaceSpecialization A q 1 data hKr k red hα hβ`, which carries a map `P.sp` from places of `modularFunctionFieldBar 1` to places of `modularFunctionFieldC k 1`, a homomorphism on degree-zero divisor classes, and the compatibility laws of that structure. The finite set $W$ of places of `modularFunctionFieldC k 1` is required by `hW` to consist exactly of the members of `ssPlaces q 1 k`, the supersingular places. Finally `R : ProlongationTuple P` provides two regular prolongations `R.R₁`, `R.R₂` of $A$ to `modularFunctionFieldBar (1 * q)` with residue fields in `modularFunctionFieldFullC (ResidueField A) 1` and the reduction maps `R.residue₁`, `R.residue₂` into `modularFunctionFieldC k 1`.
--
--   The model hypotheses on $R$ are: `hR`, i.e. `R.IsModel` (the conjunction of `R.DivisorLawFst`, `R.DivisorLawSnd`, `R.CuspLawInfty`, `R.CuspLawZero`); `hRL`, i.e. `R.RegularityLaw W` (non-negativity of the orders of the two residues at a place $v$ fixed by the square of `frobOnPlacesGeomLevel` and affine, and existence of a common value at each node pair, whenever $f$ has non-negative order at all places above); `hNV`, i.e. `R.NodeValueLaw W` (for $f$ with both residues non-zero and a node pair $s$ met by no place in the support of $\operatorname{div} f$, the two residues take a common non-zero value at $s.1$ and $s.2$); and `hO`, i.e. `R.OrderLawFixed` (the push-forward along `P.reduceFst` of the divisor of $f$ at such a place $v$ equals $\operatorname{ord}_v$ of the first residue plus $\operatorname{ord}$ of the second residue at `frobOnPlacesGeomLevel` of $v$).
--
--   The annulus datum `dat : R.AnnulusDatumQ W` consists of intermediate fields `dat.K w` of $\overline{\mathbb Q}/\mathbb Q$, node coordinates `dat.coord w hw` over `dat.K w` for $w \in W$, widths `dat.width w`, rational depths `dat.depthQ V` indexed by places $V$ of `modularFunctionFieldBar (1 * q)`, a distinguished place `dat.cusp`, uniformisers `dat.unifFst w`, `dat.unifSnd w` in `modularFunctionFieldC k 1`, and units `dat.u0 w`, `dat.lam w`, `dat.mu w` of $k$. Its hypotheses are: `hwidth`, $1 \le$ `dat.width w` for $w \in W$; `hwidthj`, `dat.width w` equals `jWidth` of `w.evalAt (jGeomGen k 1)`, i.e. $3$, $2$ or $1$ according as the $j$-value at $w$ is $0$, $1728$, or neither; `hdepthQ`, for $w \in W$ and every place $V$ with `P.reduceFst V = w` which is neither `P.IsStrictFst` nor `P.IsStrictSnd` (these predicates say that `frobOnPlacesGeomLevel` carries `P.reduceFst V` to `P.reduceSnd V`, respectively `P.reduceSnd V` to `P.reduceFst V`, while the relevant place is not fixed by the square of `frobOnPlacesGeomLevel`), one has $0 <$ `dat.depthQ V` $<$ `dat.width w` together with the cleared depth–value identity `(dat.coord w hw).yDepth V ^ (dat.depthQ V).den` $=$ `A.valuation (q : AlgebraicClosure ℚ) ^ (dat.depthQ V).num.toNat`, where `yDepth V` is the $A$-valuation of `V.evalAt` of the $y$-coordinate; `hdepthσ`, invariance of `dat.depthQ` under the action through `arithmeticGalois (modularFunctionFieldFull (1 * q))` of the inertia subgroup `A.inertiaSubgroupIn ℚ`; `hcusp`, `dat.cusp ∉ W`, and `hcuspφ`, `dat.cusp` is fixed by `arithFrobC q k 1`; `hunif`, for $w \in W$ the divisor of `dat.unifFst w` is $(w) - (\mathtt{dat.cusp})$ and that of `dat.unifSnd w` is $(\mathtt{arithFrobC } q\, k\, 1 \cdot w) - (\mathtt{dat.cusp})$, both expressed as equalities of $\operatorname{ord}$ at every place; and `hKfix`, every element of `dat.K w` ($w \in W$) is fixed by every element of `A.inertiaSubgroupIn ℚ`; each `dat.K w` is finite over $\mathbb Q$.
--
--   The local node hypotheses, all for $w \in W$, concern the coefficient ring `NodeLocalized.coeffSubring A (dat.K w)` $= A \cap$ `dat.K w` and the ring `R.nodeIntegersOver (dat.K w) w`: `ϖ` is a chosen element of the coefficient ring and `hϖ` says that `NodeLocalized.redRestrict red (dat.K w) d = 0` holds precisely when `ϖ w` divides $d$; `eK w \ge 1` by `heK`, `ε w` is a unit by `hε`, `hqϖ` factors $q = (\varpi_w)^{e_K(w)} \varepsilon_w$ in the coefficient ring and `hε1` says `ε w` reduces to $1$; `u w hw` is a unit of `R.nodeIntegersOver (dat.K w) w` with $x \cdot y =$ `R.nodeConst (dat.K w) w (ϖ w) ^ (dat.width w * eK w)` $\cdot\, u$ (hypothesis `hu`), where $x, y$ are the coordinates of `dat.coord w hw`; `hmax` says the ideal spanned by the image of `ϖ w` and by $x, y$ is maximal and is the only maximal ideal; `hbr` says the spans of $\{\varpi_w, x\}$ and of $\{\varpi_w, y\}$ are prime with $y$ outside the first and $x$ outside the second (the two branches through the node); `hnoeth` makes `R.nodeIntegersOver (dat.K w) w` Noetherian; `hres` says that for every $g$ in that ring some constant $o$ from the coefficient ring makes $g -$ `R.nodeConst (dat.K w) w o` a non-unit; `hVI` imposes `R.ValueIntegralityLaw w`, i.e. `V.evalAt f ∈ A` for $f \in$ `R.nodeIntegers w` and $V$ with `P.reduceFst V = w`. The three value-pinning hypotheses are `hu0`, `hlam` and `hmu`: `R.nodeResidue₁ w` of $u$ takes the value `dat.u0 w` at $w$; `R.nodeResidue₁ w` of $y$ divided by `dat.unifFst w` takes the value `dat.lam w` at $w$; and `R.nodeResidue₂ w` of $x$ divided by `dat.unifSnd w` takes the value `dat.mu w` at `arithFrobC q k 1 • w`. Here `v.HasValue g a` means $g$ lies in the valuation ring of $v$ and its residue is the image of $a \in k$.
--
--   Next, $D$ is an element of the group of degree-zero divisors of `modularFunctionFieldBar (1 * q)`, subject to `hDstab`, stability of $D$ under the `arithmeticGalois`-action of `A.inertiaSubgroupIn ℚ`, and `hDsupp`, every place in its support is `P.IsStrictFst`, or `P.IsStrictSnd`, or reduces under `P.reduceFst` into $W$. A twist vector `a : ProlongationTuple.TwistVector W` (integers `aZ`, `aZ'` and a family `aE`) is related to $D$ by `ha : dat.IsTwistOf a D`, which asserts that the degree of `P.fstDiv D` (the restriction of $D$ to the `P.IsStrictFst` places) is $-\sum_{w \in W}$ `dat.endOrderFst a D w`, that the degree of `P.sndDiv D` is $-\sum_{w \in W}$ `dat.endOrderSnd a D w`, and that for $w \in W$ and $1 \le d$ with $d + 1 \le$ `dat.width w` the circle degree `dat.circleDeg D w d` equals minus the second difference `dat.chainVal a w (d-1) - 2 dat.chainVal a w d + dat.chainVal a w (d+1)`; here `dat.endOrderFst a D w` $=$ `dat.endSlopeFst a w + dat.endShareFst D w` and `dat.endOrderSnd a D w` $=$ `dat.endSlopeSnd a w + dat.endShareSnd D w`. The specialisation datum `dat.spData a D` is the triple consisting of the push-forward of `P.fstDiv D` along `P.reduceFst` corrected at `dat.cusp` so as to have degree zero, the push-forward of `P.sndDiv D` along `P.reduceSnd` corrected in the same way, and the node unit family `dat.nodeUnitOf a D`; `hadm` places it in `GluingData.admissible (nodePairsOfPlaces (arithFrobC q k 1) W)`, i.e. both divisor components have degree zero and vanish at the first, respectively second, member of every node pair, and `hsp` says that its class in `GluedPic0 (nodePairsOfPlaces (arithFrobC q k 1) W)` is zero.
--
--   Finally, $d_1, d_2$ are natural numbers, $Q_1 : \mathrm{Fin}\,d_1$ and $Q_2 : \mathrm{Fin}\,d_2$ are families of places of `modularFunctionFieldBar (1 * q)` with all $Q_1(i)$ satisfying `P.IsStrictFst` (`hQ₁`) and all $Q_2(j)$ satisfying `P.IsStrictSnd` (`hQ₂`), $E$ is an effective divisor ($0 \le E$, hypothesis `hE0`), and $f \ne 0$ is an element of `modularFunctionFieldBar (1 * q)` whose divisor is prescribed by `hdivf`: at every place $V$, $\bigl(E - \sum_i (Q_1(i)) - \sum_j (Q_2(j)) - D\bigr)(V) = \operatorname{ord}_V f$. The hypothesis `hker` identifies the kernel of $red$ with the maximal ideal of $A$.
--
--   Under these hypotheses there exists a rational number $\delta$ with the following three properties.
--
--   First: for every $c \in \overline{\mathbb Q}$ with $c \cdot f \in$ `R.R₁.integers` and `R.R₁.residue ⟨c • f⟩` $\ne 0$, and every $w \in W$,
--   $$\delta \le \mathtt{dat.width } w \cdot \bigl(\operatorname{ord}_w(\mathtt{R.residue₁ } \langle c \cdot f\rangle) + \mathtt{dat.endOrderFst } a\, D\, w\bigr)$$
--   as an inequality in $\mathbb Q$.
--
--   Second: for every $c \in \overline{\mathbb Q}$ with $c \cdot f \in$ `R.R₂.integers` and `R.R₂.residue ⟨c • f⟩` $\ne 0$, and every $w \in W$,
--   $$-\,\mathtt{dat.width } w \cdot \bigl(\operatorname{ord}_{\mathtt{arithFrobC } q\,k\,1 \cdot w}(\mathtt{R.residue₂ } \langle c \cdot f\rangle) + \mathtt{dat.endOrderSnd } a\, D\, w\bigr) \le \delta .$$
--
--   Third: there exist $c_1, c_2 \in \overline{\mathbb Q}$ with $c_1 \cdot f \in$ `R.R₁.integers`, $c_2 \cdot f \in$ `R.R₂.integers`, with `R.R₁.residue ⟨c₁ • f⟩` $\ne 0$ and `R.R₂.residue ⟨c₂ • f⟩` $\ne 0$, such that for all $g_1, g_2 \in$ `modularFunctionFieldC k 1` and all families $av, bv$ of units of $k$ indexed by `nodePairsOfPlaces (arithFrobC q k 1) W` satisfying: the first component of `dat.spData a D` is the divisor of $g_1$ (an equality of $\operatorname{ord}$ at every place), the second component is the divisor of $g_2$, for every node pair $s$ one has $s.1$`.HasValue` $g_1\,(av\,s)$ and $s.2$`.HasValue` $g_2\,(bv\,s)$, and the third component of `dat.spData a D` is the family $s \mapsto$ `Additive.ofMul (av s / bv s)` — then for every $w \in W$, if $\delta = 0$ and
--   $$\operatorname{ord}_{\mathtt{arithFrobC } q\,k\,1 \cdot w}(\mathtt{R.residue₂ } \langle c_2 \cdot f\rangle) + \mathtt{dat.endOrderSnd } a\, D\, w = 0,$$
--   it follows that
--   $$\operatorname{ord}_w(\mathtt{R.residue₁ } \langle c_1 \cdot f\rangle) + \mathtt{dat.endOrderFst } a\, D\, w = 0$$
--   and that there is a unit $c$ of $k$ for which the element
--   $$\mathtt{R.residue₁ } \langle c_1 \cdot f\rangle \cdot g_1 \cdot \prod_{w' \in W} (\mathtt{dat.unifFst } w')^{\mathtt{dat.endOrderFst } a\, D\, w'}$$
--   has value $c$ at $w$, while
--   $$\mathtt{R.residue₂ } \langle c_2 \cdot f\rangle \cdot g_2 \cdot \prod_{w' \in W} (\mathtt{dat.unifSnd } w')^{\mathtt{dat.endOrderSnd } a\, D\, w'}$$
--   has value $c$ at `arithFrobC q k 1 • w` — the same unit $c$ on both sheets.
--
--   This is the value clause in the analysis of the two-component special fibre of the modular curve of level $q$ at $q$, where the two copies of the $j$-line are glued at the supersingular places of $W$: a single rational number $\delta$ simultaneously bounds the width-weighted end orders of the reduction of $f$ on the first sheet from below and on the second sheet from above, and in the boundary case $\delta = 0$ the two end orders vanish together and the two reductions, normalised by the products of uniformisers to the end orders, take one and the same value in $k^\times$ at the glued pair $(w, \mathrm{Frob}_q \cdot w)$. It is used by [`ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumQ.exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumQ.exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_endOrder_ineq_and_coupledScalings_hasValue_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.lean

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

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumQ.exists_endOrder_ineq_and_coupledScalings_hasValue_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable
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

      (∃ (c₁ : AlgebraicClosure ℚ) (h₁ : c₁ • f ∈ R.R₁.integers) (c₂ : AlgebraicClosure ℚ) (h₂ : c₂ • f ∈ R.R₂.integers),
        R.R₁.residue ⟨c₁ • f, h₁⟩ ≠ 0 ∧ R.R₂.residue ⟨c₂ • f, h₂⟩ ≠ 0 ∧
        ∀ (g₁ g₂ : ↥(modularFunctionFieldC k 1))
          (av bv : ↥(nodePairsOfPlaces (arithFrobC q k 1) W) → kˣ),
          (∀ v, (dat.spData a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))).1 v = v.ord g₁) →
          (∀ v, (dat.spData a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))).2.1 v = v.ord g₂) →
          (∀ s : ↥(nodePairsOfPlaces (arithFrobC q k 1) W),
            (s : Place k ↥(modularFunctionFieldC k 1) × Place k ↥(modularFunctionFieldC k 1)).1.HasValue g₁ (av s) ∧
            (s : Place k ↥(modularFunctionFieldC k 1) × Place k ↥(modularFunctionFieldC k 1)).2.HasValue g₂ (bv s)) →
          ((dat.spData a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))).2.2 = fun s => Additive.ofMul (av s / bv s)) →
          ∀ w ∈ W, δ = 0 →
            (arithFrobC q k 1 • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩) + dat.endOrderSnd a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w = 0 →
            (w.ord (R.residue₁ ⟨c₁ • f, h₁⟩) + dat.endOrderFst a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w = 0 ∧
             ∃ c : kˣ, w.HasValue (R.residue₁ ⟨c₁ • f, h₁⟩ * g₁ * ∏ w' ∈ W, dat.unifFst w' ^ dat.endOrderFst a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w') (c : k) ∧
               (arithFrobC q k 1 • w).HasValue
                 (R.residue₂ ⟨c₂ • f, h₂⟩ * g₂ * ∏ w' ∈ W, dat.unifSnd w' ^ dat.endOrderSnd a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) w') (c : k))) := by sorry
