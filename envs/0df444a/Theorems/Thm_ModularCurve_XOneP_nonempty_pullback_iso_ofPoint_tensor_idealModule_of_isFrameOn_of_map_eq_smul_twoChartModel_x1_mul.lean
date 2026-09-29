-- Prove2me | Theorems.Thm_ModularCurve_XOneP_nonempty_pullback_iso_ofPoint_tensor_idealModule_of_isFrameOn_of_map_eq_smul_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.nonempty_pullback_iso_ofPoint_tensor_idealModule_of_isFrameOn_of_map_eq_smul_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/ecf446cf-83ef-59eb-b0c3-720932842749
-- title:
--   Generic fibre of a crossing-glued module on X₁(Mp)
-- statement:
--   Fix a prime $p$, an integer $M\ge 5$ with $p\nmid M$, a characteristic-zero field $L$ that is a $\{p\}$-cyclotomic extension of $\mathbb Q$ with a primitive $p$-th root of unity $\zeta$, and let $K\subseteq \mathrm{LaurentSeries}\,L$ be the intermediate field obtained by adjoining to $L$ the image of the function field [`ModularCurve.x1FunctionField (M * p)`](def/ModularCurve_X1.html#L137) under the coefficientwise embedding; let $A$ be a discrete valuation domain with fraction field $L$ such that $p$ lies in $\mathfrak m_A$ and $\zeta$ is in the image of $A$, with compatible $A$-algebra structure on $K$, and let $j\in K$ be the element whose Laurent expansion is the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) of the modular invariant, $j\neq 0$. Write $X_S$ for the pullback of the two-chart model [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252) $\to\operatorname{Spec}A$ along a base $S$. Further data, all assumed: an algebraically closed field $k$ of characteristic $p$ over $A$, two proper smooth relative-dimension-one geometrically integral $k$-curves $C_1,C_2$ closed-immersed over $k$ into $X_k$ whose images cover $X_k$, with $C_1\times_{X_k}C_2$ reduced of cardinality $n>0$; a uniformiser $\varpi$ of $A$; a valuation subring $\mathrm{Pl}$ of $\overline{\mathbb Q}$ with $p$ a non-unit, a ring map $\rho:A\to \mathrm{Pl}$ inducing the structure map to $\overline{\mathbb Q}$, a surjection $\pi_k:\mathrm{Pl}\to k$ with $\pi_k\circ\rho$ the structure map, comparison morphisms $bc:X_k\to X_{\mathrm{Pl}}$ and $j_\eta:X_{\overline{\mathbb Q}}\to X_{\mathrm{Pl}}$ commuting with both projections, properness of the model, and two $\overline{\mathbb Q}$-points $\bar y_1,\bar y_2$ of the model over $\operatorname{Spec}A$. Finally, for some $e\ge 1$, an open $U\subseteq X_{\mathrm{Pl}}$ with a $\mathrm{Pl}$-morphism $f:U\to \operatorname{Spec}\bigl(\mathrm{Pl}[X_0,X_1]/(X_0X_1-\rho(\varpi)^e)\bigr)$, an open $W_{\mathrm{et}}\subseteq U$ on which $f$ is étale, and two sections $s,s'$ of $U\to\operatorname{Spec}\mathrm{Pl}$ with closed points in $W_{\mathrm{et}}$, such that $j_\eta$ carries the graphs of $\bar y_2,\bar y_1$ to $s,s'$ after base change to $\overline{\mathbb Q}$, and such that $f\circ s$, $f\circ s'$ are given by the crossing-algebra lifts sending $(X_0,X_1)$ to $(x',y')$ and to $(wx',w^{-1}y')$, where $x',y'\in\mathfrak m_{\mathrm{Pl}}$ satisfy $x'y'=\rho(\varpi)^e$ and $w\in\mathrm{Pl}^\times$; $s'$ is assumed determined by $f\circ s'$. Put $a=X_0-x'$, $b=y'-X_1$, $a_w=X_0-wx'$, $b_w=y'-wX_1$ in the global sections of the crossing scheme $\mathrm{Mdl}$ and $O=(D(a)\cup D(b))\cap(D(a_w)\cup D(b_w))$. The assertion is: for every $g\in\Gamma(\mathrm{Mdl},D(a)\cup D(b))$ with $g\,a=a_w$ on $D(a)$, $g\,b=b_w$ on $D(b)$ and $g$ a unit on $O$, for all opens $W_2,W_3$ of $X_{\mathrm{Pl}}$ with $W_2\cup W_3=\top$, $W_2\subseteq U$, $W_2\cap W_3\subseteq U_\iota(f^{-1}O)$ and $W_3$ exactly the complement of the images of $s$ and $s'$, setting $t\in\Gamma(X_{\mathrm{Pl}},W_2\cap W_3)$ to be the pullback of $g|_O$ under $f$ transported through $U_\iota$: for every module $\mathcal L$ on $X_{\mathrm{Pl}}$ and sections $a_{\mathcal L}\in\Gamma(\mathcal L,W_2)$, $b_{\mathcal L}\in\Gamma(\mathcal L,W_3)$ that are frames on $W_2$ resp. $W_3$ (multiplication by the restricted section is a bijection from structure sections to $\mathcal L$-sections on every smaller open) and satisfy $b_{\mathcal L}=t\cdot a_{\mathcal L}$ on $W_2\cap W_3$, the pullback of $\mathcal L$ along $j_\eta$ is isomorphic to the tensor product of the dual of the ideal-sheaf module of the relative effective Cartier divisor cut out by the graph of $\bar y_1$ with the ideal-sheaf module of the divisor cut out by the graph of $\bar y_2$.
--
--   This is the generic-fibre half of the construction of the annulus (inertia) line bundle on the two-chart model of $X_1(Mp)$ at a place above $p$: a module glued from frames on two opens with transition function read off from a crossing chart $X_0X_1=\rho(\varpi)^e$ is identified, after pullback to the $\overline{\mathbb Q}$-fibre, with $\mathcal O(\bar y_1)\otimes\mathcal I(\bar y_2)$. It feeds the statement producing simultaneously an invertible pullback isomorphism and a trivialisation for the reduction of the model at a crossing point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_nonempty_pullback_iso_ofPoint_tensor_idealModule_of_isFrameOn_of_map_eq_smul_twoChartModel_x1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra AlgebraicGeometry.SmoothProperCurve
open MvPolynomial

theorem ModularCurve.XOneP.nonempty_pullback_iso_ofPoint_tensor_idealModule_of_isFrameOn_of_map_eq_smul_twoChartModel_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra A k]
    (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)) (i₂ : SchemeHomOver c₂ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hred : IsReduced (pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n)
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})

    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))
    (πk : ↥Pl →+* k) (hAlgk : algebraMap A k = πk.comp ρ) (hπk : Function.Surjective πk)

    (bc : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρ)))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom πk))

    [IsProper (ModularCurve.TwoChart.modelTo A (↥K) j)]
    (jη : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρ)))
    (hjη₁ : jη ≫ pullback.fst _ _ = pullback.fst _ _)
    (hjη₂ : jη ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom Pl.subtype))

    (ybar₁ ybar₂ : SchemeHomOver (specMap A (AlgebraicClosure ℚ)) (ModularCurve.TwoChart.modelTo A (↥K) j))

    (e : ℕ) (he : 1 ≤ e)
    (U : (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρ))).Opens)
    (f : (U : Scheme.{0}) ⟶ CrossingQuotient.crossingScheme ((ρ ϖ) ^ e))
    (hf : f ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥Pl (CrossingQuotient ↥Pl ((ρ ϖ) ^ e)))) =
      U.ι ≫ pullback.snd _ _)

    (Wet : (U : Scheme.{0}).Opens) [AlgebraicGeometry.Etale (Wet.ι ≫ f)]

    (sU sU' : Spec (CommRingCat.of ↥Pl) ⟶ (U : Scheme.{0}))
    (hsU : sU ≫ U.ι ≫ pullback.snd _ _ = 𝟙 _) (hsU' : sU' ≫ U.ι ≫ pullback.snd _ _ = 𝟙 _)
    (hsW : sU.base (IsLocalRing.closedPoint ↥Pl) ∈ Wet) (hsW' : sU'.base (IsLocalRing.closedPoint ↥Pl) ∈ Wet)
    (hP₂ : graphOver (ModularCurve.TwoChart.modelTo A (↥K) j) ybar₂.1 ybar₂.2 ≫ jη = Spec.map (CommRingCat.ofHom Pl.subtype) ≫ sU ≫ U.ι)
    (hP₁ : graphOver (ModularCurve.TwoChart.modelTo A (↥K) j) ybar₁.1 ybar₁.2 ≫ jη = Spec.map (CommRingCat.ofHom Pl.subtype) ≫ sU' ≫ U.ι)

    (x' y' : ↥Pl) (hxy : x' * y' = (ρ ϖ) ^ e)
    (hx' : x' ∈ IsLocalRing.maximalIdeal ↥Pl) (hy' : y' ∈ IsLocalRing.maximalIdeal ↥Pl) (w : (↥Pl)ˣ)

    (hxyw : ((w : ↥Pl) * x') * ((↑w⁻¹ : ↥Pl) * y') = algebraMap ↥Pl ↥Pl ((ρ ϖ) ^ e))
    (hxy₁ : x' * y' = algebraMap ↥Pl ↥Pl ((ρ ϖ) ^ e))
    (hfs : sU ≫ f = Spec.map (CommRingCat.ofHom (CrossingQuotient.lift (t := (ρ ϖ) ^ e) x' y' hxy₁).toRingHom))
    (hfs' : sU' ≫ f = Spec.map (CommRingCat.ofHom
      (CrossingQuotient.lift (t := (ρ ϖ) ^ e) ((w : ↥Pl) * x') ((↑w⁻¹ : ↥Pl) * y') hxyw).toRingHom))

    (huq : sU' ≫ f = sU ≫ f → sU' = sU) :
    letI X : Scheme.{0} := pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρ))
    letI Q := CrossingQuotient ↥Pl ((ρ ϖ) ^ e)
    letI Mdl : Scheme.{0} := CrossingQuotient.crossingScheme ((ρ ϖ) ^ e)
    letI φ : Q →+* Γ(Mdl, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom
    letI a : Γ(Mdl, ⊤) := φ (CrossingQuotient.U _ - algebraMap ↥Pl Q x')
    letI b : Γ(Mdl, ⊤) := φ (algebraMap ↥Pl Q y' - CrossingQuotient.V _)
    letI aw : Γ(Mdl, ⊤) := φ (CrossingQuotient.U _ - algebraMap ↥Pl Q ((w : ↥Pl) * x'))
    letI bw : Γ(Mdl, ⊤) := φ (algebraMap ↥Pl Q y' - algebraMap ↥Pl Q (w : ↥Pl) * CrossingQuotient.V _)
    letI O : Mdl.Opens := (Mdl.basicOpen a ⊔ Mdl.basicOpen b) ⊓ (Mdl.basicOpen aw ⊔ Mdl.basicOpen bw)

    ∀ (gM : Γ(Mdl, Mdl.basicOpen a ⊔ Mdl.basicOpen b)),
      Mdl.presheaf.map (homOfLE (le_sup_left : Mdl.basicOpen a ≤ Mdl.basicOpen a ⊔ Mdl.basicOpen b)).op gM *
          Mdl.presheaf.map (homOfLE (le_top : Mdl.basicOpen a ≤ ⊤)).op a =
        Mdl.presheaf.map (homOfLE (le_top : Mdl.basicOpen a ≤ ⊤)).op aw →
      Mdl.presheaf.map (homOfLE (le_sup_right : Mdl.basicOpen b ≤ Mdl.basicOpen a ⊔ Mdl.basicOpen b)).op gM *
          Mdl.presheaf.map (homOfLE (le_top : Mdl.basicOpen b ≤ ⊤)).op b =
        Mdl.presheaf.map (homOfLE (le_top : Mdl.basicOpen b ≤ ⊤)).op bw →
      IsUnit (Mdl.presheaf.map (homOfLE (inf_le_left : O ≤ Mdl.basicOpen a ⊔ Mdl.basicOpen b)).op gM) →

    ∀ (W₂ W₃ : X.Opens), W₂ ⊔ W₃ = ⊤ → W₂ ≤ U → ∀ (hle : W₂ ⊓ W₃ ≤ U.ι ''ᵁ (f ⁻¹ᵁ O)),
    (∀ z, z ∈ W₃ ↔ (z ∉ Set.range (sU ≫ U.ι).base ∧ z ∉ Set.range (sU' ≫ U.ι).base)) →
    letI t : Γ(X, W₂ ⊓ W₃) := X.presheaf.map (homOfLE hle).op
      ((U.ι.appIso (f ⁻¹ᵁ O)).inv (f.app O (Mdl.presheaf.map (homOfLE (inf_le_left : O ≤ Mdl.basicOpen a ⊔ Mdl.basicOpen b)).op gM)))

    ∀ (L : X.Modules) (aL : Γ(L, W₂)) (bL : Γ(L, W₃)),
      Scheme.Modules.IsFrameOn aL W₂ → Scheme.Modules.IsFrameOn bL W₃ →
      L.presheaf.map (homOfLE (inf_le_right : W₂ ⊓ W₃ ≤ W₃)).op bL =
        t • L.presheaf.map (homOfLE (inf_le_left : W₂ ⊓ W₃ ≤ W₂)).op aL →
      Nonempty ((Scheme.Modules.pullback jη).obj L ≅
        (RelEffCartierDiv.ofPoint (ModularCurve.TwoChart.modelTo A (↥K) j) ybar₁.1 ybar₁.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (ModularCurve.TwoChart.modelTo A (↥K) j) ybar₂.1 ybar₂.2).idealModule) := by sorry
