-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumLevel_mapDomain_fstDiv_eq_and_mapDomain_sndDiv_eq_of_mk_spData_eq_zero_of_pin
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumLevel.mapDomain_fstDiv_eq_and_mapDomain_sndDiv_eq_of_mk_spData_eq_zero_of_pin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/e5b7a634-188b-5fe2-b6ad-c544bd41c38c
-- title:
--   Pinned strict reductions of a Jacobi-inversion divisor at level N
-- statement:
--   Throughout, $q$ is a prime, $A$ is a valuation subring of $\overline{\mathbb{Q}}$, $N$ is a positive integer, $k$ is an algebraically closed field of characteristic $q$, and $red : A \to k$ is a ring homomorphism; `data` is a `ModularPolynomialData` for $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ killing the pair $(j, j_q)$) subject to the Kronecker congruence `hKr`, namely $\Phi \bmod q = (X^q - Y)(X - Y^q)$ in the bivariate reduction, and `hα`, `hβ` assert that the two Hecke degeneracy embeddings $\bar\alpha, \bar\beta$ of the level-$Nq$ modular function field over $\overline{\mathbb{Q}}$ are integral. Given such data, $P$ is a `PlaceSpecialization`, i.e. a specialisation of places of $\overline{\mathbb{Q}}$-modular function fields to places over $k$ together with a map on degree-zero divisor classes satisfying the listed compatibilities, and $q \nmid N$ is assumed (`hqN`). Places of the field `modularFunctionFieldC k N` play the role of closed points of $X_0(N)$ over $k$, and places of `modularFunctionFieldBar (N * q)` the role of closed points of $X_0(Nq)$ over $\overline{\mathbb{Q}}$; $P$ supplies the two reduction maps `P.reduceFst`, `P.reduceSnd` (restriction along $\bar\alpha$, resp. $\bar\beta$, followed by `P.sp`), and the two strictness predicates: `P.IsStrictFst V` says that the geometric Frobenius `frobOnPlacesGeomLevel` sends `P.reduceFst V` to `P.reduceSnd V` while its square does not fix `P.reduceFst V`, and `P.IsStrictSnd V` says that `P.reduceFst V` is the Frobenius image of `P.reduceSnd V` while the square of Frobenius does not fix `P.reduceSnd V`. For a divisor $D$ on the level-$Nq$ curve, `P.fstDiv D` and `P.sndDiv D` are the restrictions of $D$ to the places satisfying `P.IsStrictFst`, resp. `P.IsStrictSnd`.
--
--   The finite set $W$ of places of `modularFunctionFieldC k N` is required (`hW`) to consist exactly of the supersingular places `ssPlaces q N k`. The tuple $R$ is a `ProlongationTuple` for $P$ — a pair of regular prolongations $R_1, R_2$ of $A$ to the level-$Nq$ field with residue field the level-$N$ modular function field over the residue field of $A$, together with the comparison homomorphisms — and four groups of hypotheses on it are imposed: `hR` that $R$ is a model (the two divisor laws and the two cusp laws), `hRL` the regularity law on $W$ (non-negativity of the orders of the residues at affine Frobenius-square-fixed places where $f$ has no poles above, and existence of a common value at each node pair), `hNV` the node-value law on $W$ (for $f$ with non-zero residues and a node pair $s$ avoided by the divisor of $f$, the two residues take one and the same non-zero value at $s_1$ and $s_2$), `hO` the fixed-order law (for $f$ with non-zero residues on both sides, the push-forward of the divisor of $f$ along `P.reduceFst` at an affine place $v$ fixed by the square of Frobenius equals $\mathrm{ord}_v$ of the first residue plus $\mathrm{ord}$ at the Frobenius image of $v$ of the second residue), and `hVI` the value-integrality law at each $w \in W$ (for $f$ in the node integers at $w$, the value of $f$ at every place $V$ with `P.reduceFst V = w` lies in $A$).
--
--   The object `dat` is an `AnnulusDatumLevel` for $R$ and $W$: a family of intermediate fields $K(w) \subseteq \overline{\mathbb{Q}}$, node coordinates $(x,y)$ at each $w \in W$ over $K(w)$, widths $\mathrm{width}(w) \in \mathbb{N}$, a rational depth function $\mathrm{depthQ}$ on places of the level-$Nq$ curve, uniformisers $\mathrm{unifFst}(w)$, $\mathrm{unifSnd}(w)$ with correction divisors $\mathrm{corrFst}(w)$, $\mathrm{corrSnd}(w)$, and units $u_0(w), \lambda(w), \mu(w) \in k^\times$. Its law block consists of: `hwidth`, $1 \le \mathrm{width}(w)$ for $w \in W$; `hwidthc`, $\mathrm{width}(w) =$ `placeWidthChar q N w` for $w \in W$; `hdepthQ`, for $w \in W$ and every place $V$ with `P.reduceFst V = w` which is neither strict-first nor strict-second, $0 < \mathrm{depthQ}(V) < \mathrm{width}(w)$ and the $y$-depth $\mathrm{val}_A(V(y))$ raised to the denominator of $\mathrm{depthQ}(V)$ equals $\mathrm{val}_A(q)$ raised to its numerator; `hdepthσ`, invariance of $\mathrm{depthQ}$ under the inertia subgroup of $A$ over $\mathbb{Q}$ acting through `arithmeticGalois`; `hD1`, for each $w \in W$ of width at least $2$ the existence of an inertia-fixed place $V$ above $w$, neither strict-first nor strict-second, with $\mathrm{depthQ}(V) = 1$; `hunif`, for $w \in W$ that the divisor of $\mathrm{unifFst}(w)$ is $(w) + \mathrm{corrFst}(w)$ with $\mathrm{corrFst}(w)$ vanishing on $W$ and of degree $-1$, and the divisor of $\mathrm{unifSnd}(w)$ is $(\mathrm{arithFrobC}\,q\,k\,N \cdot w) + \mathrm{corrSnd}(w)$ with $\mathrm{corrSnd}(w)$ vanishing on $W$ and of degree $-1$; `hKfix`, that inertia fixes $K(w)$ pointwise for $w \in W$; and `hK`, that each $K(w)$ is finite over $\mathbb{Q}$.
--
--   Further data are chosen: elements $\varpi(w)$ and $\varepsilon(w)$ of the coefficient subring $A \cap K(w)$, integers $e_K(w) \in \mathbb{N}$, and, for $w \in W$, elements $u(w)$ of the node integers `R.nodeIntegersOver (dat.K w) w` over $K(w)$. These satisfy the local block at each $w \in W$, summarised here clause by clause: `hϖ`, an element of the coefficient subring reduces to $0$ under `NodeLocalized.redRestrict red (dat.K w)` exactly when it is a multiple of $\varpi(w)$; `heK`, $1 \le e_K(w)$; `hε`, $\varepsilon(w)$ is a unit; `hqϖ`, the image of $q$ in the coefficient subring is $\varpi(w)^{e_K(w)}\varepsilon(w)$; `hε1`, $\varepsilon(w)$ reduces to $1$; `hu`, $u(w)$ is a unit and $x\,y = \mathrm{nodeConst}(\varpi(w))^{\mathrm{width}(w)\,e_K(w)}\,u(w)$ for the node coordinates $x = (\mathrm{coord}\,w)\!.x$, $y = (\mathrm{coord}\,w)\!.y$; `hmax`, the ideal generated by $\mathrm{nodeConst}(\varpi(w)), x, y$ is maximal and is the only maximal ideal of the node integers at $w$; `hbr`, the ideals generated by $\{\mathrm{nodeConst}(\varpi(w)), x\}$ and $\{\mathrm{nodeConst}(\varpi(w)), y\}$ are prime, with $y$ outside the first and $x$ outside the second; `hnoeth`, the node integers at $w$ are Noetherian; `hres`, for every element $g$ of the node integers there is a coefficient constant $o$ with $g - \mathrm{nodeConst}(o)$ a non-unit; `hu0`, the first node residue of $u(w)$ has value $u_0(w)$ at $w$; `hlam`, the quotient of the first node residue of $y$ by $\mathrm{unifFst}(w)$ has value $\lambda(w)$ at $w$; and `hmu`, the quotient of the second node residue of $x$ by $\mathrm{unifSnd}(w)$ has value $\mu(w)$ at $\mathrm{arithFrobC}\,q\,k\,N \cdot w$. Here a place $v$ "has value $c$" at a function means the function lies in the valuation subring of $v$ and its residue is the image of $c$.
--
--   Next, $X$ is a degree-zero divisor on the level-$Nq$ curve over $\overline{\mathbb{Q}}$, assumed inertia-stable (`hXstab`: fixed by $\mathrm{arithmeticGalois}(\sigma)$ for every $\sigma$ in the inertia subgroup of $A$ over $\mathbb{Q}$) and with support (`hXsupp`) contained in the places which are strict-first, strict-second, or whose first reduction lies in $W$. A twist vector $a = (a_Z, a_{Z'}, a_E)$ of type `TwistVectorLevel W` is given with `ha : dat.IsTwistOf a X`, that is: the degree of `P.fstDiv X` equals minus the sum over $w \in W$ of the first end orders $\mathrm{endOrderFst}(a, X, w)$, the degree of `P.sndDiv X` equals minus the corresponding sum of second end orders, and for $w \in W$ and $1 \le d$ with $d + 1 \le \mathrm{width}(w)$ the circle degree $\mathrm{circleDeg}(X, w, d)$ equals minus the second difference $\mathrm{chainVal}(a,w,d-1) - 2\,\mathrm{chainVal}(a,w,d) + \mathrm{chainVal}(a,w,d+1)$. The associated gluing datum $\mathrm{spData}(a, X)$ — the triple consisting of the push-forward of `P.fstDiv X` along `P.reduceFst` minus $\sum_{w \in W} \mathrm{endOrderFst}(a,X,w)\,\mathrm{corrFst}(w)$, the push-forward of `P.sndDiv X` along `P.reduceSnd` minus $\sum_{w \in W} \mathrm{endOrderSnd}(a,X,w)\,\mathrm{corrSnd}(w)$, and the node unit $\mathrm{nodeUnitOf}(a,X)$ — is assumed admissible for the node pairs $\mathrm{nodePairsOfPlaces}(\mathrm{arithFrobC}\,q\,k\,N, W)$ (`hadm`: both divisor components of degree zero and vanishing at the respective members of each node pair) and to have class zero in the glued Picard group $\mathrm{GluedPic0}$ (`hsp`), i.e. it is glued-principal.
--
--   Finally a configuration of base points is given: families $Q_1 : \mathrm{Fin}\,d_1 \to$ places and $Q_2 : \mathrm{Fin}\,d_2 \to$ places of the level-$Nq$ curve with $Q_1(i)$ strict-first (`hQ₁`) and $Q_2(j)$ strict-second (`hQ₂`), such that $i \mapsto \mathrm{reduceFst}(Q_1 i)$ and $j \mapsto \mathrm{reduceSnd}(Q_2 j)$ are injective (`hinj₁`, `hinj₂`); finite sets $T_1$, $T_2$ of places over $k$ consisting exactly of the first reductions of the $Q_1(i)$, resp. the second reductions of the $Q_2(j)$ (`hT₁`, `hT₂`), with $T_1$ disjoint from $W$ (`hT₁W`); each place of $T_1$ and of $T_2$ is affine geometric, i.e. both $j$ and $j_N$ lie in its valuation subring (`hT₁aff`, `hT₂aff`); each such place has a centre $c \in k \times k$ (positive order of $j - c_1$ and of $j_N - c_2$) which determines it uniquely among places, and one of the two orders equals $1$ (`hT₁sm`, `hT₂sm`); the values of $j$ and of $j_N$ at the reductions of the $Q_1(i)$, resp. the $Q_2(j)$, are not fixed by $x \mapsto x^{q^2}$ (`hT₁gen`, `hT₂gen`); two non-speciality clauses hold, namely `hgp₁`, that a function on the level-$N$ curve over $k$ with non-negative order outside $T_1$, order at least $-1$ on $T_1$ and value $0$ at every $w \in W$ is zero, and `hgp₂`, that a function with non-negative order outside $T_2$ and order at least $-1$ on $T_2$ is a constant; the numerical condition `hdeg`, $d_1 + d_2 = \mathrm{genusFF}(\overline{\mathbb{Q}}, \mathrm{modularFunctionFieldBar}(Nq))$; an additional strict-first place $Q_s$ (`hQs`) whose first reduction differs from all $\mathrm{reduceFst}(Q_1 i)$ (`hQs'`); and inertia-fixedness of every $Q_1(i)$ and every $Q_2(j)$ (`hQ₁I`, `hQ₂I`). Lastly, $E$ is an effective divisor ($0 \le E$) and $f \ne 0$ a function on the level-$Nq$ curve with
--   $$\mathrm{div}(f) \;=\; E - \Big(\sum_i (Q_1 i) + \sum_j (Q_2 j)\Big) - X$$
--   placewise (`hdivf`).
--
--   Under these hypotheses the conclusion is the conjunction of two equalities of divisors on the level-$N$ curve over $k$: first, the push-forward along `P.reduceFst` of the strict-first part `P.fstDiv E` of $E$ equals $\sum_i (\mathrm{reduceFst}(Q_1 i))$, each of the $d_1$ distinct points occurring with coefficient exactly $1$; second, the push-forward along `P.reduceSnd` of the strict-second part `P.sndDiv E` of $E$ equals $\sum_j (\mathrm{reduceSnd}(Q_2 j))$, again with all coefficients $1$.
--
--   This is the pinning statement for the level-$N$ annulus chart: it says that the effective divisor produced by Jacobi inversion against a prescribed inertia-fixed configuration of base points reduces, on each of the two copies of $X_0(N)$ in characteristic $q$, precisely onto the reductions of those base points, with multiplicity one. It is used by [`ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumLevel.exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumLevel.exists_isGoodDiv_pic0Mk_eq_of_isTwistOf_of_mk_spData_eq_zero_of_inertiaStable), in the analysis of the semistable reduction of $X_0(Nq)$ at $q$ and of the specialisation of divisor classes which underlies the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumLevel_mapDomain_fstDiv_eq_and_mapDomain_sndDiv_eq_of_mk_spData_eq_zero_of_pin.lean

import Mathlib
import Definitions.Def_ModularCurve_AnnulusSpecializationLevel
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization
open Classical in

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumLevel.mapDomain_fstDiv_eq_and_mapDomain_sndDiv_eq_of_mk_spData_eq_zero_of_pin
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
    (X : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))))
    (hXstab : ∀ σ ∈ A.inertiaSubgroupIn ℚ,
        arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) = X)
    (hXsupp : ∀ V ∈ (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))).support, P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W)
    (a : ProlongationTuple.TwistVectorLevel (k := k) (N := N) W)
    (ha : dat.IsTwistOf a (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))))
    (hadm : dat.spData a (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k N) W))
    (hsp : GluedPic0.mk (nodePairsOfPlaces (arithFrobC q k N) W) ⟨dat.spData a (X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))), hadm⟩ = 0)
    {d₁ d₂ : ℕ}
    (Q₁ : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (Q₂ : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hQ₁ : ∀ i, P.IsStrictFst (Q₁ i)) (hQ₂ : ∀ j, P.IsStrictSnd (Q₂ j))
    (hinj₁ : Function.Injective fun i => P.reduceFst (Q₁ i))
    (hinj₂ : Function.Injective fun j => P.reduceSnd (Q₂ j))
    {T₁ T₂ : Finset (Place k ↥(modularFunctionFieldC k N))}
    (hT₁ : ∀ v, v ∈ T₁ ↔ ∃ i, P.reduceFst (Q₁ i) = v)
    (hT₂ : ∀ v, v ∈ T₂ ↔ ∃ j, P.reduceSnd (Q₂ j) = v)
    (hT₁W : Disjoint T₁ W)
    (hT₁aff : ∀ v ∈ T₁, IsAffineGeomPlace k N v) (hT₂aff : ∀ v ∈ T₂, IsAffineGeomPlace k N v)
    (hT₁sm : ∀ v ∈ T₁, ∃ c : k × k, IsCentreOf k N c v ∧
      (∀ v' : Place k ↥(modularFunctionFieldC k N), IsCentreOf k N c v' → v' = v) ∧
      (v.ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.1) = 1 ∨
        v.ord (jNGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.2) = 1))
    (hT₂sm : ∀ v ∈ T₂, ∃ c : k × k, IsCentreOf k N c v ∧
      (∀ v' : Place k ↥(modularFunctionFieldC k N), IsCentreOf k N c v' → v' = v) ∧
      (v.ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.1) = 1 ∨
        v.ord (jNGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.2) = 1))
    (hT₁gen : ∀ i, (P.reduceFst (Q₁ i)).evalAt (jGeomGen k N) ^ (q ^ 2) ≠ (P.reduceFst (Q₁ i)).evalAt (jGeomGen k N) ∧
      (P.reduceFst (Q₁ i)).evalAt (jNGeomGen k N) ^ (q ^ 2) ≠ (P.reduceFst (Q₁ i)).evalAt (jNGeomGen k N))
    (hT₂gen : ∀ j, (P.reduceSnd (Q₂ j)).evalAt (jGeomGen k N) ^ (q ^ 2) ≠ (P.reduceSnd (Q₂ j)).evalAt (jGeomGen k N) ∧
      (P.reduceSnd (Q₂ j)).evalAt (jNGeomGen k N) ^ (q ^ 2) ≠ (P.reduceSnd (Q₂ j)).evalAt (jNGeomGen k N))
    (hgp₁ : ∀ h : ↥(modularFunctionFieldC k N),
      (∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ T₁ → 0 ≤ v.ord h) → (∀ v ∈ T₁, -1 ≤ v.ord h) →
      (∀ w ∈ W, w.HasValue h 0) → h = 0)
    (hgp₂ : ∀ h : ↥(modularFunctionFieldC k N),
      (∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ T₂ → 0 ≤ v.ord h) → (∀ v ∈ T₂, -1 ≤ v.ord h) →
      ∃ c : k, h = algebraMap k ↥(modularFunctionFieldC k N) c)
    (hdeg : d₁ + d₂ = genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (Qs : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hQs : P.IsStrictFst Qs)
    (hQs' : ∀ i, P.reduceFst Qs ≠ P.reduceFst (Q₁ i))
    (hQ₁I : ∀ i, ∀ σ ∈ A.inertiaSubgroupIn ℚ,
      arithmeticGalois (modularFunctionFieldFull (N * q)) σ • Q₁ i = Q₁ i)
    (hQ₂I : ∀ j, ∀ σ ∈ A.inertiaSubgroupIn ℚ,
      arithmeticGalois (modularFunctionFieldFull (N * q)) σ • Q₂ j = Q₂ j)
    (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hE0 : 0 ≤ E)
    (f : ↥(modularFunctionFieldBar (N * q))) (hf0 : f ≠ 0)
    (hdivf : ∀ V, (E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ))
      - (X : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))) V = V.ord f) :
    Finsupp.mapDomain P.reduceFst (P.fstDiv E) = ∑ i, Finsupp.single (P.reduceFst (Q₁ i)) (1 : ℤ) ∧
      Finsupp.mapDomain P.reduceSnd (P.sndDiv E) = ∑ j, Finsupp.single (P.reduceSnd (Q₂ j)) (1 : ℤ) := by sorry
