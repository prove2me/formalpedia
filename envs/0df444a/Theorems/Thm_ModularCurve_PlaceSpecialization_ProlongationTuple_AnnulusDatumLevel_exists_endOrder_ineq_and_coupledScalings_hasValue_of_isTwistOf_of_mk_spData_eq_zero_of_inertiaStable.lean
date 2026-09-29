-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumLevel_exists_endOrder_ineq_and_coupledScalings_hasValue_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumLevel.exists_endOrder_ineq_and_coupledScalings_hasValue_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/490f41a1-1242-5d6e-803f-b3430c3f2ff5
-- title:
--   Chord bounds and coupled rigidity along supersingular annuli of X₀(Nq)
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, an integer $N \neq 0$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $\mathrm{red} : A \to k$, modular polynomial data `data` for $q$ satisfying the Kronecker congruence `hKr`, and the two Hecke integrality hypotheses $h\alpha$, $h\beta$ asserting that the ring maps underlying `heckeAlphaBar` and `heckeBetaBar` for level $N$ and prime $q$ over $\overline{\mathbb{Q}}$ are integral. Let $P$ be a place specialization of that data ($P :$ `PlaceSpecialization A q N data hKr k red hα hβ`), and assume $q \nmid N$ (`hqN`). Let $W$ be a finite set of places of the geometric modular function field `modularFunctionFieldC k N` over $k$ which, by `hW`, consists exactly of the supersingular places `ssPlaces q N k`.
--
--   Let $R$ be a prolongation tuple for $P$, so in particular $R$ carries two regular prolongations $R_1$, $R_2$ of $A$ in `modularFunctionFieldBar (N * q)` with values in `modularFunctionFieldFullC (ResidueField A) N`, together with the comparison map $\iota$ into `modularFunctionFieldC k N`; the derived residue maps into the geometric function field are written `R.residue₁`, `R.residue₂`. The hypotheses on $R$ are: `hR`, that $R$ is a model (the conjunction of the two divisor laws and the two cusp laws at $\infty$ and at $0$); `hRL`, the regularity law over $W$ (non-negativity of the orders of the two residues at Frobenius-stable affine geometric places where $f$ has no poles above them, and existence of a common value of the two residues at each node pair when $f$ is regular above the first component); `hNV`, the node value law over $W$ (for $f$ integral for both prolongations with nonzero residues, and a node pair $s$ above which $f$ has no zeros or poles, the two residues take a common nonzero value at $s_1$ and $s_2$); `hO`, the fixed order law (at a Frobenius-stable affine geometric place $v$ the $\mathrm{reduceFst}$-pushforward of $\mathrm{div} f$ at $v$ equals $\operatorname{ord}_v$ of the first residue plus $\operatorname{ord}$ at the geometric Frobenius image of $v$ of the second residue); and `hVI`, the value integrality law at every $w \in W$ (node integers at $w$ have values in $A$ at every place above $w$).
--
--   Let `dat : R.AnnulusDatumLevel W` be a level-$N$ annulus datum, i.e. the data of intermediate fields $K(w) \subseteq \overline{\mathbb{Q}}$ over $\mathbb{Q}$, node coordinates `coord w hw` over $K(w)$ for $w \in W$, widths `width w`, a depth function `depthQ` on the places of `modularFunctionFieldBar (N * q)` with rational values, uniformisers `unifFst w`, `unifSnd w` in `modularFunctionFieldC k N`, correction divisors `corrFst w`, `corrSnd w`, and units `u0 w`, `lam w`, `mu w` of $k$. The law block imposed on `dat` is the following, and every clause is listed. Widths: `hwidth`, $1 \leq \mathrm{width}\,w$ for $w \in W$; `hwidthc`, $\mathrm{width}\,w =$ `placeWidthChar q N w`, the quotient of `jWidthChar q` of the value of the $j$-generator `jGeomGen k N` at $w$ by `placeRamificationJ N w`. Depths: `hdepthQ`, for $w \in W$ and every place $V$ of `modularFunctionFieldBar (N * q)` over $\overline{\mathbb{Q}}$ with $\mathrm{reduceFst}\,V = w$ which is neither strict of the first kind nor strict of the second kind, $0 < \mathrm{depthQ}\,V < \mathrm{width}\,w$ and the $y$-depth $A$-valuation $(\mathrm{coord}\,w\,hw).\mathrm{yDepth}\,V$ raised to the denominator of $\mathrm{depthQ}\,V$ equals the $A$-valuation of $q$ raised to the numerator of $\mathrm{depthQ}\,V$; `hdepthσ`, invariance of `depthQ` under the action of `arithmeticGalois (modularFunctionFieldFull (N * q)) σ` for every $\sigma$ in the inertia subgroup `A.inertiaSubgroupIn ℚ` (the image of the inertia subgroup of $A$ inside the $\mathbb{Q}$-automorphisms of $\overline{\mathbb{Q}}$); `hD1`, for each $w \in W$ of width at least $2$ there is a place $V$ above $w$, non-strict of both kinds, fixed by the whole inertia action, with $\mathrm{depthQ}\,V = 1$. Uniformisers: `hunif`, for $w \in W$ the divisor of $\mathrm{unifFst}\,w$ is $\delta_w + \mathrm{corrFst}\,w$ with $\mathrm{corrFst}\,w$ vanishing on $W$ and of degree $-1$, and the divisor of $\mathrm{unifSnd}\,w$ is $\delta_{\varphi w} + \mathrm{corrSnd}\,w$ with $\mathrm{corrSnd}\,w$ vanishing on $W$ and of degree $-1$, where $\varphi =$ `arithFrobC q k N` acts on places. Coefficient fields: `hKfix`, every element of $K(w)$ is fixed by inertia for $w \in W$; `hK`, each $K(w)$ is finite over $\mathbb{Q}$.
--
--   Further data are supplied at each place: elements $\varpi(w)$ and $\varepsilon(w)$ of the coefficient subring `NodeLocalized.coeffSubring A (K w)` $= A \cap K(w)$, natural numbers $e_K(w)$, and elements $u(w, hw)$ of the node integers `R.nodeIntegersOver (K w) w`, subject to: `hϖ`, $\varpi(w)$ generates the kernel of `NodeLocalized.redRestrict red (K w)` (an element reduces to $0$ exactly when it is a multiple of $\varpi(w)$); `heK`, $1 \leq e_K(w)$; `hε`, $\varepsilon(w)$ is a unit; `hqϖ`, $q = \varpi(w)^{e_K(w)}\varepsilon(w)$ in the coefficient subring; `hε1`, $\varepsilon(w)$ reduces to $1$; `hu`, $u(w,hw)$ is a unit and the product of the two node coordinates equals `R.nodeConst (K w) w (ϖ w)` raised to $\mathrm{width}\,w \cdot e_K(w)$ times $u(w,hw)$; `hmax`, the ideal spanned by the constant $\varpi(w)$ and the two coordinates is maximal and is the only maximal ideal of the node integers; `hbr`, the ideals spanned by $\varpi(w)$ together with one coordinate are prime and each coordinate lies outside the span of $\varpi(w)$ and the other coordinate; `hnoeth`, the node integers at $w$ form a Noetherian ring; `hres`, for every $g$ in the node integers some constant $o$ makes $g -$ `R.nodeConst (K w) w o` a non-unit. Residual normalisations: `hu0`, the first node residue of $u(w,hw)$ has value $u_0(w)$ at $w$; `hlam`, the first node residue of the $y$-coordinate divided by $\mathrm{unifFst}\,w$ has value $\mathrm{lam}(w)$ at $w$; `hmu`, the second node residue of the $x$-coordinate divided by $\mathrm{unifSnd}\,w$ has value $\mathrm{mu}(w)$ at $\varphi w$.
--
--   Let $D$ be a divisor of degree zero on `modularFunctionFieldBar (N * q)` over $\overline{\mathbb{Q}}$, stable under the inertia action (`hDstab`) and supported on places that are strict of the first kind, strict of the second kind, or reduce into $W$ (`hDsupp`). Let $a$ be a twist vector `TwistVectorLevel W`, that is integers $a_Z$, $a_{Z'}$ and a family $a_E(w,d)$ of integers; the associated chain value is $\mathrm{chainVal}\,a\,w\,d = a_Z$ for $d = 0$, $a_{Z'}$ for $d \geq \mathrm{width}\,w$, and $a_E(w,d)$ otherwise, the end slopes are $\mathrm{chainVal}\,a\,w\,1 - \mathrm{chainVal}\,a\,w\,0$ and $\mathrm{chainVal}\,a\,w\,(\mathrm{width}\,w - 1) - \mathrm{chainVal}\,a\,w\,(\mathrm{width}\,w)$, and the end orders $\mathrm{endOrderFst}\,a\,D\,w$, $\mathrm{endOrderSnd}\,a\,D\,w$ add to these slopes the end shares, the numerators of the circle degrees $\mathrm{circleDeg}\,D\,w\,0$ and $\mathrm{circleDeg}\,D\,w\,(\mathrm{width}\,w)$ when those have denominator $1$ and $0$ otherwise, where $\mathrm{circleDeg}\,D\,w\,d = \sum_V D(V)\max(0, 1 - |\mathrm{depthQ}\,V - d|)$ over the places $V$ in the support of $D$ above $w$ that are non-strict of both kinds. The hypothesis `ha` states that $a$ is a twist of $D$: the degree of `P.fstDiv D` is $-\sum_{w \in W} \mathrm{endOrderFst}\,a\,D\,w$, the degree of `P.sndDiv D` is $-\sum_{w \in W} \mathrm{endOrderSnd}\,a\,D\,w$, and for $w \in W$ and $1 \leq d$ with $d + 1 \leq \mathrm{width}\,w$ the circle degree $\mathrm{circleDeg}\,D\,w\,d$ equals minus the second difference $\mathrm{chainVal}\,a\,w\,(d-1) - 2\,\mathrm{chainVal}\,a\,w\,d + \mathrm{chainVal}\,a\,w\,(d+1)$. The gluing datum $\mathrm{spData}\,a\,D$, consisting of the $\mathrm{reduceFst}$-pushforward of `P.fstDiv D` minus $\sum_{w \in W} \mathrm{endOrderFst}\,a\,D\,w \cdot \mathrm{corrFst}\,w$, the $\mathrm{reduceSnd}$-pushforward of `P.sndDiv D` minus $\sum_{w \in W} \mathrm{endOrderSnd}\,a\,D\,w \cdot \mathrm{corrSnd}\,w$, and the unit family $\mathrm{nodeUnitOf}\,a\,D$ built from $u_0$, $\mathrm{lam}$, $\mathrm{mu}$, the angular and crossing factors of `dat` and the end orders, is assumed admissible for the node pairs `nodePairsOfPlaces (arithFrobC q k N) W` (`hadm`: both divisor components have degree zero and vanish at the respective components of every node pair), and its class in `GluedPic0` is assumed to be zero (`hsp`), i.e. the gluing datum is glued principal.
--
--   Finally, a Jacobi section is fixed: natural numbers $d_1$, $d_2$, families $Q_1 : \mathrm{Fin}\,d_1 \to$ places and $Q_2 : \mathrm{Fin}\,d_2 \to$ places of `modularFunctionFieldBar (N * q)` with every $Q_1(i)$ strict of the first kind (`hQ₁`) and every $Q_2(j)$ strict of the second kind (`hQ₂`), an effective divisor $E \geq 0$ (`hE0`), and a nonzero function $f$ (`hf0`) whose divisor is $E - \sum_i Q_1(i) - \sum_j Q_2(j) - D$, in the sense that this divisor takes the value $\operatorname{ord}_V f$ at every place $V$ (`hdivf`). The hypothesis `hker` states that $\mathrm{red}$ has kernel exactly the maximal ideal of $A$.
--
--   Under these hypotheses there exists a rational number $\delta$ with the following three properties.
--
--   First, for every scalar $c \in \overline{\mathbb{Q}}$ such that $c \cdot f$ lies in the integers of $R_1$ and has nonzero $R_1$-residue, and every $w \in W$,
--   $$\delta \leq \mathrm{width}\,w \cdot \bigl(\operatorname{ord}_w(\mathrm{residue}_1(c \cdot f)) + \mathrm{endOrderFst}\,a\,D\,w\bigr).$$
--
--   Second, for every scalar $c$ such that $c \cdot f$ lies in the integers of $R_2$ and has nonzero $R_2$-residue, and every $w \in W$,
--   $$-\,\mathrm{width}\,w \cdot \bigl(\operatorname{ord}_{\varphi w}(\mathrm{residue}_2(c \cdot f)) + \mathrm{endOrderSnd}\,a\,D\,w\bigr) \leq \delta .$$
--
--   Third, there is one coupled pair of scalars $c_1$, $c_2$ with $c_1 \cdot f$ in the integers of $R_1$ and $c_2 \cdot f$ in the integers of $R_2$, both with nonzero residues, such that the following holds for all $g_1, g_2$ in `modularFunctionFieldC k N` and all families $av, bv$ of units of $k$ indexed by the node pairs which realise the glued principality of $\mathrm{spData}\,a\,D$, namely: the first component of $\mathrm{spData}\,a\,D$ is the divisor of $g_1$ and the second is the divisor of $g_2$, each node pair $s$ satisfies that $s_1$ has value $av(s)$ on $g_1$ and $s_2$ has value $bv(s)$ on $g_2$, and the third component of $\mathrm{spData}\,a\,D$ is $s \mapsto \mathrm{Additive.ofMul}(av(s)/bv(s))$. For such $g_1, g_2, av, bv$, for every $w \in W$, if $\delta = 0$ and $\operatorname{ord}_{\varphi w}(\mathrm{residue}_2(c_2 \cdot f)) + \mathrm{endOrderSnd}\,a\,D\,w = 0$, then $\operatorname{ord}_w(\mathrm{residue}_1(c_1 \cdot f)) + \mathrm{endOrderFst}\,a\,D\,w = 0$ and there is a single unit $c$ of $k$ such that $w$ has value $c$ on
--   $$\mathrm{residue}_1(c_1 \cdot f) \cdot g_1 \cdot \prod_{w' \in W} (\mathrm{unifFst}\,w')^{\mathrm{endOrderFst}\,a\,D\,w'}$$
--   and $\varphi w$ has the same value $c$ on
--   $$\mathrm{residue}_2(c_2 \cdot f) \cdot g_2 \cdot \prod_{w' \in W} (\mathrm{unifSnd}\,w')^{\mathrm{endOrderSnd}\,a\,D\,w'} .$$
--
--   This is the level-$N$ chord inequality together with the rigidity statement for the twisted Gauss valuation profiles of a function on the supersingular annuli of $X_0(Nq)$: the two inequalities bound the end orders of the reductions of all admissible scalings of $f$ by a single rational slope $\delta$, and in the flat case $\delta = 0$ the two reductions glue, up to the uniformiser correction, to a single value at each node pair. It is used by [`ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumLevel.mapDomain_fstDiv_eq_and_mapDomain_sndDiv_eq_of_mk_spData_eq_zero_of_pin`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumLevel.mapDomain_fstDiv_eq_and_mapDomain_sndDiv_eq_of_mk_spData_eq_zero_of_pin), where the resulting equalities of end orders are converted into identities between the pushforwards of the two halves of the divisor $D$ on the special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumLevel_exists_endOrder_ineq_and_coupledScalings_hasValue_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable.lean

import Mathlib
import Definitions.Def_ModularCurve_AnnulusSpecializationLevel
import Definitions.Def_ModularCurve_PlaceWidthChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization
open Classical in

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumLevel.exists_endOrder_ineq_and_coupledScalings_hasValue_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
    {W : Finset (Place k (modularFunctionFieldC k N))}
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (hO : R.OrderLawFixed) (hVI : ∀ w ∈ W, R.ValueIntegralityLaw w)
    (dat : R.AnnulusDatumLevel W)
    (hwidth : ∀ w ∈ W, 1 ≤ dat.width w)
    (hwidthc : ∀ w ∈ W, dat.width w = placeWidthChar q N w)
    (hdepthQ : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
      (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
      P.reduceFst V = w → ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V →
      0 < dat.depthQ V ∧ dat.depthQ V < dat.width w ∧ (dat.coord w hw).yDepth V ^ (dat.depthQ V).den =
      A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ^ (dat.depthQ V).num.toNat)
    (hdepthσ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      dat.depthQ (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V) = dat.depthQ V)
    (hD1 : ∀ w ∈ W, 2 ≤ dat.width w → ∃ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V ∧
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V) ∧ dat.depthQ V = 1)
    (hunif : ∀ w ∈ W,
      ((∀ v, (Finsupp.single w (1 : ℤ) + dat.corrFst w) v = v.ord (dat.unifFst w)) ∧ (∀ v ∈ W, dat.corrFst w v = 0) ∧
      Divisor.degree (dat.corrFst w) = -1) ∧
      ((∀ v, (Finsupp.single (arithFrobC q k N • w) (1 : ℤ) + dat.corrSnd w) v = v.ord (dat.unifSnd w)) ∧
      (∀ v ∈ W, dat.corrSnd w v = 0) ∧ Divisor.degree (dat.corrSnd w) = -1))
    (hKfix : ∀ w ∈ W, ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ z ∈ dat.K w, σ z = z)
    (hK : ∀ w : Place k (modularFunctionFieldC k N), FiniteDimensional ℚ ↥(dat.K w))
    (ϖ : ∀ w : Place k (modularFunctionFieldC k N), ↥(NodeLocalized.coeffSubring A (dat.K w)))
      (eK : Place k (modularFunctionFieldC k N) → ℕ)
      (ε : ∀ w : Place k (modularFunctionFieldC k N), ↥(NodeLocalized.coeffSubring A (dat.K w)))
      (u : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W), ↥(R.nodeIntegersOver (dat.K w) w))
    (hϖ : ∀ w ∈ W, ∀ d : ↥(NodeLocalized.coeffSubring A (dat.K w)),
      NodeLocalized.redRestrict red (dat.K w) d = 0 ↔ ∃ d', d = ϖ w * d')
    (heK : ∀ w ∈ W, 1 ≤ eK w)
    (hε : ∀ w ∈ W, IsUnit (ε w))
    (hqϖ : ∀ w ∈ W, ((q : ℕ) : ↥(NodeLocalized.coeffSubring A (dat.K w))) = ϖ w ^ eK w * ε w)
    (hε1 : ∀ w ∈ W, NodeLocalized.redRestrict red (dat.K w) (ε w) = 1)
    (hu : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W), IsUnit (u w hw) ∧
      (dat.coord w hw).x * (dat.coord w hw).y = R.nodeConst (dat.K w) w (ϖ w) ^ (dat.width w * eK w) * u w hw)
    (hmax : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W),
      (Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).x, (dat.coord w hw).y}).IsMaximal ∧
      ∀ M : Ideal ↥(R.nodeIntegersOver (dat.K w) w), M.IsMaximal →
      M = Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).x, (dat.coord w hw).y})
    (hbr : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W),
      (Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).x}).IsPrime ∧
      (Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).y}).IsPrime ∧
      (dat.coord w hw).y ∉ Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).x} ∧
      (dat.coord w hw).x ∉ Ideal.span {R.nodeConst (dat.K w) w (ϖ w), (dat.coord w hw).y})
    (hnoeth : ∀ w ∈ W, IsNoetherianRing ↥(R.nodeIntegersOver (dat.K w) w))
    (hres : ∀ w ∈ W, ∀ g : ↥(R.nodeIntegersOver (dat.K w) w),
      ∃ o : ↥(NodeLocalized.coeffSubring A (dat.K w)), ¬ IsUnit (g - R.nodeConst (dat.K w) w o))
    (hu0 : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W),
      w.HasValue (R.nodeResidue₁ w ⟨(u w hw : ↥(modularFunctionFieldBar (N * q))), (u w hw).2.1⟩) ((dat.u0 w : kˣ) : k))
    (hlam : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W),
      w.HasValue (R.nodeResidue₁ w ⟨((dat.coord w hw).y : ↥(modularFunctionFieldBar (N * q))), (dat.coord w hw).y.2.1⟩
      / dat.unifFst w) ((dat.lam w : kˣ) : k))
    (hmu : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W),
      (arithFrobC q k N • w).HasValue
      (R.nodeResidue₂ w ⟨((dat.coord w hw).x : ↥(modularFunctionFieldBar (N * q))), (dat.coord w hw).x.2.1⟩
      / dat.unifSnd w) ((dat.mu w : kˣ) : k))
    (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))))
    (hDstab : ∀ σ ∈ A.inertiaSubgroupIn ℚ,
        arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) = D)
    (hDsupp : ∀ V ∈ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).support,
      P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W)
    (a : ProlongationTuple.TwistVectorLevel (k := k) (N := N) W)
    (ha : dat.IsTwistOf a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))
    (hadm : dat.spData a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
      ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k N) W))
    (hsp : GluedPic0.mk (nodePairsOfPlaces (arithFrobC q k N) W)
      ⟨dat.spData a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))), hadm⟩ = 0)

    {d₁ d₂ : ℕ}
    (Q₁ : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (Q₂ : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hQ₁ : ∀ i, P.IsStrictFst (Q₁ i)) (hQ₂ : ∀ j, P.IsStrictSnd (Q₂ j))
    (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hE0 : 0 ≤ E)
    (f : ↥(modularFunctionFieldBar (N * q))) (hf0 : f ≠ 0)
    (hdivf : ∀ V, (E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ))
      - (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))) V = V.ord f)

    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    :
    ∃ δ : ℚ,

      (∀ (c : AlgebraicClosure ℚ) (h : c • f ∈ R.R₁.integers), R.R₁.residue ⟨c • f, h⟩ ≠ 0 →
        ∀ w ∈ W, δ ≤ (dat.width w : ℚ) * ((w.ord (R.residue₁ ⟨c • f, h⟩) : ℚ) + (dat.endOrderFst a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) w : ℚ))) ∧

      (∀ (c : AlgebraicClosure ℚ) (h : c • f ∈ R.R₂.integers), R.R₂.residue ⟨c • f, h⟩ ≠ 0 →
        ∀ w ∈ W, -((dat.width w : ℚ) * (((arithFrobC q k N • w).ord (R.residue₂ ⟨c • f, h⟩) : ℚ)
          + (dat.endOrderSnd a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) w : ℚ))) ≤ δ) ∧

      (∃ (c₁ : AlgebraicClosure ℚ) (h₁ : c₁ • f ∈ R.R₁.integers) (c₂ : AlgebraicClosure ℚ) (h₂ : c₂ • f ∈ R.R₂.integers),
        R.R₁.residue ⟨c₁ • f, h₁⟩ ≠ 0 ∧ R.R₂.residue ⟨c₂ • f, h₂⟩ ≠ 0 ∧
        ∀ (g₁ g₂ : ↥(modularFunctionFieldC k N))
          (av bv : ↥(nodePairsOfPlaces (arithFrobC q k N) W) → kˣ),
          (∀ v, (dat.spData a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))).1 v = v.ord g₁) →
          (∀ v, (dat.spData a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))).2.1 v = v.ord g₂) →
          (∀ s : ↥(nodePairsOfPlaces (arithFrobC q k N) W),
            (s : Place k ↥(modularFunctionFieldC k N) × Place k ↥(modularFunctionFieldC k N)).1.HasValue g₁ (av s) ∧
            (s : Place k ↥(modularFunctionFieldC k N) × Place k ↥(modularFunctionFieldC k N)).2.HasValue g₂ (bv s)) →
          ((dat.spData a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))).2.2 = fun s => Additive.ofMul (av s / bv s)) →
          ∀ w ∈ W, δ = 0 →
            (arithFrobC q k N • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩) + dat.endOrderSnd a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) w = 0 →
            (w.ord (R.residue₁ ⟨c₁ • f, h₁⟩) + dat.endOrderFst a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) w = 0 ∧
             ∃ c : kˣ, w.HasValue (R.residue₁ ⟨c₁ • f, h₁⟩ * g₁ * ∏ w' ∈ W, dat.unifFst w' ^ dat.endOrderFst a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) w') (c : k) ∧
               (arithFrobC q k N • w).HasValue
                 (R.residue₂ ⟨c₂ • f, h₂⟩ * g₂ * ∏ w' ∈ W, dat.unifSnd w' ^ dat.endOrderSnd a (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) w') (c : k))) := by sorry
