-- Prove2me | Theorems.Thm_ModularCurve_DRResolvedModelPackage_exists_nodeEquiv_swap_forall_comp_eq_dict_of_sections_of_charts
-- name    : ModularCurve.DRResolvedModelPackage.exists_nodeEquiv_swap_forall_comp_eq_dict_of_sections_of_charts
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/ad05428d-8606-5e18-b62b-82845beac997
-- title:
--   Node bijection and orientation bit for the component dictionary
-- statement:
--   Fix a prime $p \ge 5$ and a valuation subring $A$ of $\overline{\mathbb Q}$ with `hA : A.LiesOverPrime p`, i.e. $p$ lies in the set of non-units of $A$. Let $\mathfrak X$ be a `DRModelPackage p`: a Deligne–Rapoport package consisting of the two-chart integral model `DRModel p` of the modular function field of level $p$ over $\mathbb Z$ together with its properness, flatness, integrality and normality data, a curve model $M_0$ of the level-$p$ modular function field over $\mathbb Q$, a curve model $M_\eta$ of the base-changed field `modularFunctionFieldBar p` over $\overline{\mathbb Q}$, isomorphisms $e_0, e_\eta$ of these with the corresponding base changes of the integral model, Galois and compatibility clauses, the two cusp sections and the smooth locus data.
--
--   *Generic-fibre chart pin.* The open subscheme of $M_\eta$ cut out as the preimage, under $e_\eta$ followed by the first projection, of the image of the finite chart of the two-chart model is assumed non-empty, and the hypothesis `hMη` requires that for every element $a$ of the finite chart algebra `TwoChartIntegralModel.chartAlgFin ℤ (modularFunctionFieldFull p) (IgusaScheme.jFull p)`, the germ of $a$ on that open, transported into the function field of $M_\eta$ and then back along `ffEquiv.symm` into `modularFunctionFieldBar p`, has as its underlying Laurent series over $\overline{\mathbb Q}$ the coefficientwise image `coeffEmb` of the Laurent series of $a$ over $\mathbb Q$.
--
--   *Level transport between $1\cdot p$ and $p$.* An additive isomorphism `eLT : JZero (1 * p) ≃+ JZero p` of the degree-zero divisor class groups, a bijection `ePl` between the place sets of `modularFunctionFieldBar (1 * p)` and of `modularFunctionFieldBar p` over $\overline{\mathbb Q}$, and three compatibilities: `hePl`, that if a degree-zero divisor $D_2$ at level $p$ is the `Finsupp.mapDomain ePl`-image of a degree-zero divisor $D_1$ at level $1\cdot p$ then `eLT` carries the class of $D_1$ to the class of $D_2$; `hePl_fun`, that for a place $V$ at level $1\cdot p$ and functions $f$, $f'$ at the two levels with the same underlying Laurent series, $f$ lies in the valuation subring of $V$ if and only if $f'$ lies in that of $\mathrm{ePl}(V)$, and $V.\mathrm{evalAt}\,f = \mathrm{ePl}(V).\mathrm{evalAt}\,f'$; and `hePl_gal`, that `ePl` is equivariant for the arithmetic Galois actions of $\overline{\mathbb Q} \simeq_{\mathbb Q} \overline{\mathbb Q}$ at the two levels.
--
--   *Reduction datum in characteristic $p$.* An algebraically closed perfect field $k$ of characteristic $p$, a surjective ring homomorphism $\mathrm{red} : A \to k$, modular polynomial data `data` for $p$ satisfying the Kronecker congruence `hKr` (the reduction mod $p$ of the bivariate modular polynomial equals $(X^p - Y)(X - Y^p)$ in the form stated by `KroneckerCongruence`), integrality hypotheses $h\alpha$, $h\beta$ for the Hecke maps $\bar\alpha, \bar\beta$ at level $1$ and prime $p$, a place specialisation $P$ of type `PlaceSpecialization A p 1 data hKr k red hα hβ`, and a prolongation tuple $R$ over $P$. The hypotheses on $R$ are: `hqN`, that $p \nmid 1$; `hR : R.IsModel`, the conjunction of the two divisor laws and the two cusp laws; `hO : R.OrderLawFixed`, the order formula expressing, for $f$ integral for both prolongations with non-zero residues, the value of `Finsupp.mapDomain P.reduceFst` of the divisor of $f$ at a Frobenius-fixed affine geometric place as the sum of the orders of the two residues. A finite set $W$ of places of `modularFunctionFieldC k 1` is assumed, by `hW`, to consist exactly of the supersingular places `ssPlaces p 1 k`, and $R$ is assumed to satisfy the regularity law `hreg` and the node value law `hval` relative to $W$.
--
--   *Widths.* A function $e$ on places of `modularFunctionFieldC k 1` with $e(w) \ge 1$ for $w \in W$ (`he`) and, by `hwidth`, $e(w) = \mathrm{jWidth}(w.\mathrm{evalAt}(\mathrm{jGeomGen}\,k\,1))$ for $w \in W$, i.e. $e(w) = 3$, $2$ or $1$ according as the $j$-value of $w$ is $0$, $1728$, or neither.
--
--   *Node coordinates over a number field $K$.* A finite extension $K$ of $\mathbb Q$ inside $\overline{\mathbb Q}$; an element $\varpi$ of the coefficient subring $A \cap K$ whose multiples are exactly the elements killed by the reduction `NodeLocalized.redRestrict red K` (`hϖ`); an integer $e_K \ge 1$ and a unit $\varepsilon$ of $A \cap K$ with $p = \varpi^{e_K}\varepsilon$ (`hqϖ`); for each $w \in W$ node coordinates $c_w = (x, y)$ of type `R.NodeCoordinates K w` in the ring `R.nodeIntegersOver K w`, subject to: `hxy`, that $x\,y = (\mathrm{nodeConst}_K^w \varpi)^{e(w) e_K} u$ for some unit $u$; `hmax`, that the ideal generated by $\mathrm{nodeConst}_K^w\varpi$, $x$ and $y$ is maximal and is the only maximal ideal of that ring; `hbr`, that the ideals generated by $\{\mathrm{nodeConst}_K^w\varpi, x\}$ and by $\{\mathrm{nodeConst}_K^w\varpi, y\}$ are prime, with $y$ outside the first and $x$ outside the second; `hnoeth`, that the ring is Noetherian; `hres`, that for every $g$ in it there is $o \in A \cap K$ with $g - \mathrm{nodeConst}_K^w o$ a non-unit; and `hVI`, the value integrality law at $w$ (every place $V$ above $w$ evaluates elements of `R.nodeIntegers w` into $A$). Finally a function `depth` on places at level $1\cdot p$ with values in $\mathbb N$ such that, by `hdepth`, each $c_w$ satisfies the depth value law: for every place $V$ with $P.\mathrm{reduceFst}\,V = w$ fixed by the arithmetic Galois action of the inertia subgroup of $A$ over $\mathbb Q$, the $y$-depth of $V$ equals the $A$-valuation of $p$ raised to the power $\mathrm{depth}(V)$.
--
--   *The charted resolved model.* Write $O$ for the valuation subring of the fixed field of the inertia subgroup `A.inertiaSubgroupIn ℚ` obtained by pulling back $A$ along the inclusion of that fixed field into $\overline{\mathbb Q}$. A ring homomorphism $\mathrm{incl} : O \to A$ is given together with `hincl`, which says that it is the obvious inclusion on underlying elements. Then $\mathfrak X_{\mathrm{reg}}$ is a `DRResolvedModelPackage p 𝔛 O k (red.comp incl)`: a regular model $Y$ over $\operatorname{Spec} O$, proper and flat with a proper morphism `toDR` to the base change of `DRModel p` to $O$, an isomorphism over the smooth locus and over the generic fibre, a finite node set with widths $\ge 1$ and a bijection `nodeEquiv` onto the crossing points of the fibre product of the two cusp components over $k$, and invertible integral ideal sheaves `comp v` indexed by $v \in$ `X0MqComponents 𝔛reg.width` $= \mathrm{Fin}\,2 \oplus \Sigma_{n}\,\mathrm{Fin}(\mathrm{width}\,n - 1)$. In addition, for every $e$ a family `Fc e : Fin (e+1) → (Resolution (p : O) e).IdealSheafData` is given, satisfying `hF`: the pullback of `Fc e k'` along the $i$-th standard chart of the resolution is the ideal sheaf generated by $V$ if $k' = i$, by $U$ if $k' = i+1$, and the unit ideal otherwise, these being the two coordinates of the crossing quotient. Finally `ch : 𝔛reg.DRResolvedModelCharts ((p : ℕ) : O) Fc` provides, at each node $n$, an open neighbourhood of the crossing point meeting no other crossing point, an étale morphism $f_n$ to the crossing scheme $uv = p^{\mathrm{width}\,n}$ over $O$ compatible with the structure morphisms, an identification of the pullback of $f_n$ along the resolution with the corresponding open of $Y$, and the labelling clause matching `comp (chainPos 𝔛reg.width n d)` with `Fc (width n) d`.
--
--   *Divisor and sections.* A degree-zero divisor $D_0$ on `modularFunctionFieldBar (1 * p)` over $\overline{\mathbb Q}$ is given which is admissible in the sense of `hadm`: every place $V'$ in its support is fixed by the arithmetic Galois action of every element of the inertia subgroup of $A$ over $\mathbb Q$, and satisfies `P.IsStrictFst V'`, or `P.IsStrictSnd V'`, or $P.\mathrm{reduceFst}\,V' \in W$ (here `IsStrictFst V'` says that Frobenius on geometric places at level $1$ carries $P.\mathrm{reduceFst}\,V'$ to $P.\mathrm{reduceSnd}\,V'$ while its square does not fix $P.\mathrm{reduceFst}\,V'$, and `IsStrictSnd V'` is the mirror condition). An integer $m$ and a bijection `idx : Fin m ≃ support D₀` enumerate the support. For each $j$ a section $\sigma_j$ of $\mathfrak X_{\mathrm{reg}}.\mathrm{toBase}$ over $\operatorname{Spec} O$ is given, such that, by `hσgen`, the base change of $\sigma_j$ along the inclusion of $O$ into $\overline{\mathbb Q}$, followed by `toDR` and the projection to `DRModel p`, equals the $\overline{\mathbb Q}$-point of $\mathfrak X.M_\eta$ corresponding under `pointEquivPlace` to the place $\mathrm{ePl}(\mathrm{idx}\,j)$, followed by $e_\eta$ and the same projection. Finally a function $v : \mathrm{Fin}\,m \to$ `X0MqComponents 𝔛reg.width` is given with `hv`: for each $j$ the image of the closed point of $\operatorname{Spec} O$ under $\sigma_j$ lies in `𝔛reg.smoothOffEdges`, lies in the support of `𝔛reg.comp (v j)`, and lies in the support of `𝔛reg.comp w` for no other $w$.
--
--   The conclusion asserts the existence of a bijection `σN : ↥W ≃ 𝔛reg.node`, of a proof that $\mathfrak X_{\mathrm{reg}}.\mathrm{width}(\sigma_N(w)) = e(w)$ for every $w \in W$, and of a Boolean `swap`, such that the following two statements hold.
--
--   First, for every $j$ the component $v_j$ is given by the dictionary: if `P.IsStrictFst (idx j)` then $v_j = \mathrm{Sum.inl}\,1$ when `swap` is true and $\mathrm{Sum.inl}\,0$ otherwise; otherwise, if `P.IsStrictSnd (idx j)` then $v_j = \mathrm{Sum.inl}\,0$ when `swap` is true and $\mathrm{Sum.inl}\,1$ otherwise; otherwise, if $w := P.\mathrm{reduceFst}(\mathrm{idx}\,j)$ lies in $W$ then $v_j = \mathrm{chainPos}\,\mathfrak X_{\mathrm{reg}}.\mathrm{width}\,(\sigma_N(w))\,d$ with $d = \mathfrak X_{\mathrm{reg}}.\mathrm{width}(\sigma_N(w)) - \mathrm{depth}(\mathrm{idx}\,j)$ when `swap` is true and $d = \mathrm{depth}(\mathrm{idx}\,j)$ otherwise, where $\mathrm{chainPos}\,\mathrm{width}\,n\,d$ is $\mathrm{Sum.inl}\,0$ for $d = 0$, $\mathrm{Sum.inr}\,\langle n, d-1\rangle$ for $0 < d < \mathrm{width}\,n$, and $\mathrm{Sum.inl}\,1$ otherwise; and in the remaining case $v_j = \mathrm{Sum.inl}\,0$.
--
--   Second, for every $j$ such that $\mathrm{idx}\,j$ is neither strict-first nor strict-second, and for every proof that $P.\mathrm{reduceFst}(\mathrm{idx}\,j) \in W$, one has $\mathrm{depth}(\mathrm{idx}\,j) \le e(P.\mathrm{reduceFst}(\mathrm{idx}\,j))$.
--
--   This is the place-to-component dictionary for the special fibre of the resolved Deligne–Rapoport model of $X_0(p)$ over the inertia-fixed valuation ring $O = A \cap \overline{\mathbb Q}^{I_A}$: it matches the supersingular places with the nodes in a width-preserving way, fixes an orientation bit distinguishing the two cusp components, and reads off, from the depth of a place, which component of the chain above a node the corresponding $O$-section meets. It feeds the construction of the sections realising a prescribed degree-zero divisor class in [`ModularCurve.DRModelPackage.exists_schemeHomOver_of_comp_eq_zero_of_abelJacobiPin_of_surjective`](thm.html#ModularCurve.DRModelPackage.exists_schemeHomOver_of_comp_eq_zero_of_abelJacobiPin_of_surjective).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRResolvedModelPackage_exists_nodeEquiv_swap_forall_comp_eq_dict_of_sections_of_charts.lean

import Mathlib
import Definitions.Def_ModularCurve_DRResolvedModelCharts
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_DRModelLegTwoInput
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian MvPolynomial MvPolynomial.CrossingQuotient
  ModularCurve AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve
open IsLocalRing ModularCurve.PlaceSpecialization

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
open Classical in

theorem ModularCurve.DRResolvedModelPackage.exists_nodeEquiv_swap_forall_comp_eq_dict_of_sections_of_charts
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime p)
    (𝔛 : DRModelPackage p)
    [hneη : Nonempty (Scheme.Opens.toScheme
      ((𝔛.eη ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))) ⁻¹ᵁ
        ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)))]
    (hMη : ∀ a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
      ((𝔛.Mη.ffEquiv.symm
          (𝔛.Mη.C.germToFunctionField
            ((𝔛.eη ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))) ⁻¹ᵁ
              ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))
            (((𝔛.eη ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))).app
                ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
              (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of
                  ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a))))
          : ↥(modularFunctionFieldBar p)) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ))

    (eLT : JZero (1 * p) ≃+ JZero p)
    (ePl : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ≃ Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p))
    (hePl : ∀ (D₁ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * p)))))
        (D₂ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar p)))),
      (D₂ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)) =
          Finsupp.mapDomain ePl (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))) →
      eLT (Pic0.mk D₁) = Pic0.mk D₂)
    (hePl_fun : ∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)))
        (f : ↥(modularFunctionFieldBar (1 * p))) (f' : ↥(modularFunctionFieldBar p)),
      (f : LaurentSeries (AlgebraicClosure ℚ)) = (f' : LaurentSeries (AlgebraicClosure ℚ)) →
        (f ∈ V.toValuationSubring ↔ f' ∈ (ePl V).toValuationSubring) ∧ V.evalAt f = (ePl V).evalAt f')
    (hePl_gal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))),
      ePl (arithmeticGalois (modularFunctionFieldFull (1 * p)) σ • V) = arithmeticGalois (modularFunctionFieldFull p) σ • ePl V)

    {k : Type} [Field k] [CharP k p] [PerfectField k] [IsAlgClosed k] {red : A →+* k}
    (hred : Function.Surjective red)
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    (P : PlaceSpecialization A p 1 data hKr k red hα hβ)
    (R : ProlongationTuple P) [DecidableEq k] (hqN : ¬ p ∣ 1)
    (hR : R.IsModel) (hO : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k 1)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces p 1 k)
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W)
    (e : Place k (modularFunctionFieldC k 1) → ℕ) (he : ∀ w ∈ W, 1 ≤ e w)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (eK : ℕ) (heK : 1 ≤ eK) (ε : ↥(NodeLocalized.coeffSubring A K)) (hε : IsUnit ε)
    (hqϖ : ((p : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε)
    (cs : ∀ w ∈ W, R.NodeCoordinates K w)
    (hxy : ∀ w (hw : w ∈ W), ∃ u : ↥(R.nodeIntegersOver K w), IsUnit u ∧
        (cs w hw).x * (cs w hw).y = R.nodeConst K w ϖ ^ (e w * eK) * u)
    (hmax : ∀ w (hw : w ∈ W),
        (Ideal.span {R.nodeConst K w ϖ, (cs w hw).x, (cs w hw).y}).IsMaximal ∧
        ∀ M : Ideal ↥(R.nodeIntegersOver K w), M.IsMaximal → M = Ideal.span {R.nodeConst K w ϖ, (cs w hw).x, (cs w hw).y})
    (hbr : ∀ w (hw : w ∈ W),
        (Ideal.span {R.nodeConst K w ϖ, (cs w hw).x}).IsPrime ∧ (Ideal.span {R.nodeConst K w ϖ, (cs w hw).y}).IsPrime ∧
        (cs w hw).y ∉ Ideal.span {R.nodeConst K w ϖ, (cs w hw).x} ∧ (cs w hw).x ∉ Ideal.span {R.nodeConst K w ϖ, (cs w hw).y})
    (hnoeth : ∀ w ∈ W, IsNoetherianRing ↥(R.nodeIntegersOver K w))
    (hres : ∀ w ∈ W, ∀ g : ↥(R.nodeIntegersOver K w),
        ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o))
    (hVI : ∀ w ∈ W, R.ValueIntegralityLaw w)
    (depth : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) → ℕ)
    (hdepth : ∀ w (hw : w ∈ W), (cs w hw).DepthValueLaw depth)
    (hwidth : ∀ w ∈ W, e w = jWidth (w.evalAt (jGeomGen k 1)))

    (incl : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) →+* ↥A)
    (hincl : ∀ o : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))), ((incl o : ↥A) : AlgebraicClosure ℚ) = algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ) (o : ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))))
    (𝔛reg : DRResolvedModelPackage p 𝔛 ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) k (red.comp incl))

    (Fc : ∀ e : ℕ, Fin (e + 1) → (Resolution ((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) e).IdealSheafData)
    (hF : ∀ (e : ℕ) (i : Fin e) (k' : Fin (e + 1)), (Fc e k').comap (Resolution.ι ((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) e i) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) ((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))))))).inv.hom
        (if (k' : ℕ) = (i : ℕ) then Ideal.span {CrossingQuotient.V ((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))))}
          else if (k' : ℕ) = (i : ℕ) + 1 then Ideal.span {CrossingQuotient.U ((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))))} else ⊤)))
    (ch : 𝔛reg.DRResolvedModelCharts ((p : ℕ) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) Fc)

    (D₀ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * p)))))
    (hadm : ∀ V' ∈ (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))).support,
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * p)) σ • V' = V') ∧
        (P.IsStrictFst V' ∨ P.IsStrictSnd V' ∨ P.reduceFst V' ∈ W))
    (m : ℕ) (idx : Fin m ≃ ↥((D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))).support))

    (σ : Fin m → SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))))) 𝔛reg.toBase)
    (hσgen : ∀ j, Spec.map (CommRingCat.ofHom ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
            (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp (RingEquiv.refl ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))).toRingHom)))) ≫ (σ j).1 ≫ 𝔛reg.toDR ≫
          pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))))) =
        ((𝔛.Mη.pointEquivPlace).symm (ePl (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))))).1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _)
    (v : Fin m → X0MqComponents 𝔛reg.width)
    (hv : ∀ j, (σ j).1.base (IsLocalRing.closedPoint ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ∈ 𝔛reg.smoothOffEdges ∧
      (σ j).1.base (IsLocalRing.closedPoint ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ∈ (𝔛reg.comp (v j)).support ∧
      ∀ w, w ≠ v j → (σ j).1.base (IsLocalRing.closedPoint ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) ∉ (𝔛reg.comp w).support) :
    ∃ (σN : ↥W ≃ 𝔛reg.node) (_ : ∀ w : ↥W, 𝔛reg.width (σN w) = e (w : Place k (modularFunctionFieldC k 1))) (swap : Bool),
      (∀ j, v j =
        (if P.IsStrictFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) then (if swap then Sum.inl 1 else Sum.inl 0)
         else if P.IsStrictSnd (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) then (if swap then Sum.inl 0 else Sum.inl 1)
         else if hw : P.reduceFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) ∈ W then
           DRResolvedModelPackage.chainPos 𝔛reg.width (σN ⟨_, hw⟩)
             (if swap then 𝔛reg.width (σN ⟨_, hw⟩) - depth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)))
              else depth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))))
         else Sum.inl 0)) ∧
      (∀ j, ¬ P.IsStrictFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) →
        ¬ P.IsStrictSnd (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) →
        ∀ hw : P.reduceFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) ∈ W,
          depth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) ≤
            e (P.reduceFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))))) := by sorry
