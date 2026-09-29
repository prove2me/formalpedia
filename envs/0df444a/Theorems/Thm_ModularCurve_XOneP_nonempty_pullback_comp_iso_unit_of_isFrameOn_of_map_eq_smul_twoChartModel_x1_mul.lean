-- Prove2me | Theorems.Thm_ModularCurve_XOneP_nonempty_pullback_comp_iso_unit_of_isFrameOn_of_map_eq_smul_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.nonempty_pullback_comp_iso_unit_of_isFrameOn_of_map_eq_smul_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/aca8aee1-0df2-59aa-bfce-c8954e15bd99
-- title:
--   Triviality on both special-fibre components of a crossing-glued module
-- statement:
--   Fix a prime $p$, an integer $M\ge 5$ with $p\nmid M$, a characteristic-zero field $L$ which is a $\{p\}$-cyclotomic extension of $\mathbb Q$, a primitive $p$-th root of unity $\zeta\in L$, and the intermediate field $K$ of $L\subseteq\mathrm{LaurentSeries}\,L$ obtained by adjoining to $L$ the image under the coefficientwise map $\mathrm{coeffEmb}$ of the function field `x1FunctionField (M * p)` of $X_1(Mp)$ inside $\mathrm{LaurentSeries}\,\mathbb Q$. Let $A$ be a discrete valuation domain with fraction field $L$, with $p$ in its maximal ideal, with $\zeta$ in the image of $A$, acting on $K$ compatibly, and let $j\in K$ be nonzero with Laurent expansion the image of the $q$-expansion `jq`. Let $k$ be an algebraically closed $A$-algebra of characteristic $p$, and let $C_1,C_2$ be proper, smooth of relative dimension $1$, geometrically integral schemes over $\operatorname{Spec} k$, equipped with closed immersions $i_1,i_2$ over $k$ into the base change along $A\to k$ of the two-chart model [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252), whose images together cover all points of that base change; the fibre product of $i_1$ and $i_2$ is assumed reduced with $n>0$ points. Fix a uniformiser $\varpi$ of $A$, a valuation subring $Pl$ of $\overline{\mathbb Q}$ with $p\in Pl.\mathrm{nonunits}$, a ring map $\rho:A\to Pl$ inducing the structure map $A\to\overline{\mathbb Q}$, and a surjection $\pi_k:Pl\to k$ with $\pi_k\circ\rho$ the structure map $A\to k$; let $bc$ be a morphism from the $k$-base change $X_k$ of the model to $X:=$ its $Pl$-base change, compatible with the first projections and with the second projections after $\operatorname{Spec}\pi_k$. Fix $e\ge 1$, an open $U\subseteq X$ and a morphism $f$ from $U$ to $\mathrm{crossingScheme}((\rho\varpi)^e)=\operatorname{Spec}\bigl(Pl[x_0,x_1]/(x_0x_1-(\rho\varpi)^e)\bigr)$ over $\operatorname{Spec} Pl$, oriented in the sense that $f$ sends points of $U$ lying in the image of $i_1$ followed by $bc$ into $V(\mathrm{V})$ and those in the image of $i_2$ followed by $bc$ into $V(\mathrm{U})$. Fix $x',y'$ in the maximal ideal of $Pl$ with $x'y'=(\rho\varpi)^e$ and a unit $w\in Pl^\times$, and put $a=\mathrm{U}-x'$, $b=y'-\mathrm{V}$, $a_w=\mathrm{U}-wx'$, $b_w=y'-w\mathrm{V}$ as global sections of $\mathrm{Mdl}=\mathrm{crossingScheme}((\rho\varpi)^e)$, and $O=(D(a)\cup D(b))\cap(D(a_w)\cup D(b_w))$. Then for every $g\in\Gamma(\mathrm{Mdl},D(a)\cup D(b))$ with $g\,a=a_w$ on $D(a)$ and $g\,b=b_w$ on $D(b)$, every pair of opens $W_2,W_3$ of $X$ with $W_2\cup W_3=\top$, $W_2\le U$ and $W_2\cap W_3\le U.\iota(f^{-1}O)$, with $t\in\Gamma(X,W_2\cap W_3)$ the section obtained by pulling back $g|_O$ along $f$ and transporting it along the isomorphism induced by the open immersion $U.\iota$, and every $X$-module $\mathcal L$ (the final binder, which reuses the name `L`) with sections $a_{\mathcal L}\in\Gamma(\mathcal L,W_2)$, $b_{\mathcal L}\in\Gamma(\mathcal L,W_3)$ that are frames on $W_2$ resp. $W_3$ — meaning that on every open $W$ contained in the relevant open, multiplication by the restricted section is a bijection $\Gamma(X,W)\to\Gamma(\mathcal L,W)$ — and satisfying $b_{\mathcal L}=t\cdot a_{\mathcal L}$ on $W_2\cap W_3$, both pullbacks of $\mathcal L$ along $i_1$ followed by $bc$ and along $i_2$ followed by $bc$ admit an isomorphism to the unit module of $C_1$, resp. $C_2$.
--
--   This is the half of the Picard–Lefschetz (vanishing-cycle) analysis of the two-chart model of $X_1(Mp)$ at a place above $p$ asserting that the module glued along the inertia cocycle $(\mathrm{U}-wx')/(\mathrm{U}-x')$ across an ordinary double point becomes trivial after restriction to each of the two components of the geometric special fibre, the transition function being constant on each branch. It feeds the statement [`ModularCurve.XOneP.exists_isInvertible_pullback_iso_ofPoint_tensor_and_pullback_iso_unit_of_reduction_crossing_of_mem_inertia_of_curveModel_igusa_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.exists_isInvertible_pullback_iso_ofPoint_tensor_and_pullback_iso_unit_of_reduction_crossing_of_mem_inertia_of_curveModel_igusa_twoChartModel_x1_mul), and is proved from the frame criterion [`AlgebraicGeometry.Scheme.Modules.IsFrameOn.nonempty_iso_tensorUnit_of_map_eq_mul`](thm.html#AlgebraicGeometry.Scheme.Modules.IsFrameOn.nonempty_iso_tensorUnit_of_map_eq_mul) together with stability of frames under pullback.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_nonempty_pullback_comp_iso_unit_of_isFrameOn_of_map_eq_smul_twoChartModel_x1_mul.lean

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

theorem ModularCurve.XOneP.nonempty_pullback_comp_iso_unit_of_isFrameOn_of_map_eq_smul_twoChartModel_x1_mul
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

    (e : ℕ) (he : 1 ≤ e)
    (U : (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρ))).Opens)
    (f : (U : Scheme.{0}) ⟶ CrossingQuotient.crossingScheme ((ρ ϖ) ^ e))
    (hf : f ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥Pl (CrossingQuotient ↥Pl ((ρ ϖ) ^ e)))) =
      U.ι ≫ pullback.snd _ _)
    (hor₃ : ∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (i₁.1 ≫ bc).base →
      CrossingQuotient.V ((ρ ϖ) ^ e) ∈ (f.base y).asIdeal)
    (hor₄ : ∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (i₂.1 ≫ bc).base →
      CrossingQuotient.U ((ρ ϖ) ^ e) ∈ (f.base y).asIdeal)

    (x' y' : ↥Pl) (hxy : x' * y' = (ρ ϖ) ^ e)
    (hx' : x' ∈ IsLocalRing.maximalIdeal ↥Pl) (hy' : y' ∈ IsLocalRing.maximalIdeal ↥Pl) (w : (↥Pl)ˣ) :
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

    ∀ (W₂ W₃ : X.Opens), W₂ ⊔ W₃ = ⊤ → W₂ ≤ U → ∀ (hle : W₂ ⊓ W₃ ≤ U.ι ''ᵁ (f ⁻¹ᵁ O)),
    letI t : Γ(X, W₂ ⊓ W₃) := X.presheaf.map (homOfLE hle).op
      ((U.ι.appIso (f ⁻¹ᵁ O)).inv (f.app O (Mdl.presheaf.map (homOfLE (inf_le_left : O ≤ Mdl.basicOpen a ⊔ Mdl.basicOpen b)).op gM)))

    ∀ (L : X.Modules) (aL : Γ(L, W₂)) (bL : Γ(L, W₃)),
      Scheme.Modules.IsFrameOn aL W₂ → Scheme.Modules.IsFrameOn bL W₃ →
      L.presheaf.map (homOfLE (inf_le_right : W₂ ⊓ W₃ ≤ W₃)).op bL =
        t • L.presheaf.map (homOfLE (inf_le_left : W₂ ⊓ W₃ ≤ W₂)).op aL →
      Nonempty ((Scheme.Modules.pullback (i₁.1 ≫ bc)).obj L ≅ SheafOfModules.unit C₁.ringCatSheaf) ∧
      Nonempty ((Scheme.Modules.pullback (i₂.1 ≫ bc)).obj L ≅ SheafOfModules.unit C₂.ringCatSheaf) := by sorry
