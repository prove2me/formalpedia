-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_points_valuationSubring_and_proj_eq_zero_smul_sub_self_of_mem_inertia_of_curveModel_igusa_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_points_valuationSubring_and_proj_eq_zero_smul_sub_self_of_mem_inertia_of_curveModel_igusa_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/05ded76c-3a27-5c36-864a-57096b89e9b9
-- title:
--   Inertia displacements on J₁(Mp) reduce into the toric part
-- statement:
--   Fix a prime $p$ and an integer $M$ with $5 \le M$ and $p \nmid M$. Let $L$ be a field of characteristic zero which is a $p$-cyclotomic extension of $\mathbb{Q}$, and $\zeta \in L$ a primitive $p$-th root of unity. Let $K$ be an intermediate field of $L \subseteq L((q))$ with $K =$ [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), that is, the subfield of the Laurent series field over $L$ generated over $L$ by the coefficientwise image of the function field of $X_1(Mp)$ over $\mathbb{Q}$. Let $A$ be a discrete valuation domain with fraction field $L$ such that $p$ lies in the maximal ideal of $A$ and $\zeta$ lies in the image of $A$, with $K$ an $A$-algebra compatibly with the tower $A \subseteq L \subseteq K$, and let $j \in K$ be the element whose Laurent expansion is the coefficientwise image of the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) of the modular invariant, assumed non-zero. All the geometry below takes place over the two-chart model [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252) of $X_1(Mp)$ over $\operatorname{Spec} A$, which is assumed proper.
--
--   The hypotheses fall into the following groups.
--
--   Special fibre. $k$ is an algebraically closed field of characteristic $p$ and an $A$-algebra; $c_1 : C_1 \to \operatorname{Spec} k$ and $c_2 : C_2 \to \operatorname{Spec} k$ are proper, smooth of relative dimension $1$ and geometrically integral; $i_1, i_2$ are closed immersions of $C_1$, $C_2$ into the base change of the model to $k$, compatible with the structure morphisms; `hcover` asserts that every point of that base change lies in the image of $i_1$ or of $i_2$; `hred` asserts that the fibre product of $i_1$ and $i_2$ is reduced, and $n$ is its cardinality, assumed positive.
--
--   Sections. $\varepsilon$ is a section of the model over $\operatorname{Spec} A$, $\varepsilon_1, \varepsilon_2$ are sections of $c_1, c_2$, and `hε₁` says that $\varepsilon_1$ followed by $i_1$ is the base change of $\varepsilon$ to $k$.
--
--   Relative Picard data. $D$ is a `RelativePic0Designation` for the model over $A$, i.e. a scheme $D.P$ with a structure morphism `D.toBase` to $\operatorname{Spec} A$ and a zero section; `hrep` asserts that $D$ represents the relative sub-Picard functor cut out by the fibrewise-algebraically-trivial condition `algEquivZeroCut` rigidified along $\varepsilon$, and `hsm`, `hsep` assert that `D.toBase` is smooth and separated. `hreps` is the corresponding representability statement for the base change of $D$ to $k$, and `hPk` the identification of its Poincaré bundle with the base change of the Poincaré bundle of $D$. Likewise $D_1$, $D_2$ are designations for $c_1$, $c_2$ with representability hypotheses `hrep₁`, `hrep₂`. Finally $\nu_2$ is a morphism from the base of the $k$-base change of $D$ to the base of $D_2$ over $\operatorname{Spec} k$, and `hν₂` requires, for every $k$-scheme $t : T \to \operatorname{Spec} k$ and every $T$-point $a$ of the $k$-base change of $D$, an isomorphism between the pullback of the Poincaré bundle of $D_2$ along $a$ followed by $\nu_2$ and the rigidification along $\varepsilon_2$ of the pullback, by the curve change morphism attached to $i_2$, of the pullback of the Poincaré bundle of the $k$-base change of $D$ along $a$.
--
--   Generic geometric fibre. There are compatible $A$- and $L$-algebra structures on $\overline{\mathbb{Q}}$; $M\eta$ is a `CurveModel` over $\overline{\mathbb{Q}}$ of the function field [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) (so a proper smooth integral curve with an identification of its function field and a bijection between closed points and places), $e\eta$ an isomorphism from its underlying scheme to the base change of the model along $\operatorname{Spec} \overline{\mathbb{Q}} \to \operatorname{Spec} A$ commuting with the structure morphisms (`heη`); the preimage under $e\eta$ followed by the first projection of the image of the finite chart is non-empty, and `hMηpin` pins the identification of function fields: for every element $a$ of the finite chart algebra [`ModularCurve.TwoChart.chartAlgFin A K j`](def/ModularCurve_TwoChartModel.html#L135), the element of [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) obtained by transporting the germ of $a$ at the generic point of that open through `Mη.ffEquiv.symm` has Laurent expansion the coefficientwise image over $\overline{\mathbb{Q}}$ of the Laurent expansion of $a$. `hgal` is Galois equivariance: for every $\mathbb{Q}$-automorphism $g$ of $\overline{\mathbb{Q}}$ fixing $L$ pointwise and all $\overline{\mathbb{Q}}$-points $x, x'$ of $M\eta$, if $x'$ followed by $e\eta$ and the first projection equals $\operatorname{Spec} g$ followed by the same composite for $x$, then the place attached to $x'$ by `Mη.pointEquivPlace` is the image of the place attached to $x$ under the semilinear automorphism [`ModularCurve.arithmeticGalois`](def/ModularCurve_ArithmeticGalois.html#L54) of $g$.
--
--   Group model of the special fibre. $G$ is a [`ModularCurve.JOneP.NeronSpecialFibreGeom p`](def/ModularCurve_JOnePGeom.html#L9): abelian groups `G.J0s`, `G.JI`, `G.JE`, a subgroup `G.torus` of `G.J0s`, and a surjective homomorphism `G.proj : G.J0s →+ G.JI × G.JE` with kernel `G.torus`. Bijections `pts`, `ptsI`, `ptsE` identify `G.J0s`, `G.JI`, `G.JE` with the $k$-points of the bases of the $k$-base change of $D$, of $D_1$ and of $D_2$; `hadd`, `haddI`, `haddE` say that each of these bijections turns addition into the tensor product of the corresponding pullbacks of the Poincaré bundle; and `hproj` says that for every $x$ in `G.J0s` the first component of `G.proj x` corresponds under `ptsI` to `pts x` followed by the morphism `RepresentsRelSubPic.pullbackHom` attached to $i_1$, and the second component corresponds under `ptsE` to `pts x` followed by $\nu_2$.
--
--   Igusa identification of the components. $w$ is an `IntegralWeightOneForm` over $k$ of level $M$, and $Mdl_1$, $Mdl_2$ are curve models over $k$ of the Igusa function field [`ModularCurve.igusaFunctionFieldX1C k M w`](def/ModularCurve_IgusaFunctionFieldX1.html#L35), together with isomorphisms $e_1 : Mdl_1.C \cong C_1$ and $e_2 : Mdl_2.C \cong C_2$ compatible with the structure morphisms.
--
--   Abel–Jacobi dictionary. `gpts` is a bijection from [`ModularCurve.JOne (M * p)`](def/ModularCurve_X1.html#L186), the degree-zero divisor class group $\operatorname{Pic}^0$ of [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) over $\overline{\mathbb{Q}}$, to the $\overline{\mathbb{Q}}$-points of the base of $D$, and `hgadd` says it is additive for the relative group law carried by the representability datum `hrep`. The remaining hypotheses `hDL`, `ajL`, `kL`, `ajbar`, `εbar`, `hPL`, `hajLε`, `hajL`, `hkL₁`, `hkL₂`, `hajbar`, `hajbar_over`, `hεbar`, `hεbar_aj`, `hpts_aj` (summarised here) provide representability of the relative sub-Picard functor over $L$, an Abel–Jacobi morphism $ajL$ over $L$ sending $\varepsilon$ to the zero section and computing, on points valued in an arbitrary field, the pullback of the Poincaré bundle as the line bundle of the point tensor the ideal module of $\varepsilon$, the comparison morphism $kL$ between the base changes to $\overline{\mathbb{Q}}$ and to $L$ and its compatibility with both projections, the induced morphism $ajbar$ from $M\eta$ to $D.P$ over $\overline{\mathbb{Q}}$ together with the $\overline{\mathbb{Q}}$-point $\varepsilon bar$ of $M\eta$ lying over $\varepsilon$ and killed by $ajbar$, and finally `hpts_aj`, which asserts that for all $\overline{\mathbb{Q}}$-points $x$ and $s$ of $M\eta$ with $s$ lying over $\varepsilon$ there is a degree-zero divisor $Dv$ equal to the difference of the one-point divisors at the places of $x$ and of $s$ whose class under `gpts` is $x$ followed by $ajbar$.
--
--   Valuation data. $Pl$ is a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit in it, $\rho : A \to Pl$ is a ring homomorphism whose composite with the inclusion of $Pl$ is the structure map $A \to \overline{\mathbb{Q}}$, and $\pi_k : Pl \to k$ is a surjective ring homomorphism with $\pi_k \circ \rho$ the structure map $A \to k$.
--
--   Under all of this, the conclusion is the following. For every $\mathbb{Q}$-automorphism $\sigma$ of $\overline{\mathbb{Q}}$ lying in `Pl.inertiaSubgroupIn ℚ` (the image in $\operatorname{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ of the inertia subgroup of $Pl$) and fixing every element of $L$, and for every class $x \in$ [`ModularCurve.JOne (M * p)`](def/ModularCurve_X1.html#L186), there exist a point $z$ of $D.P$ over $\operatorname{Spec} \rho$, i.e. a morphism $z : \operatorname{Spec} Pl \to D.P$ with $z$ followed by `D.toBase` equal to $\operatorname{Spec} \rho$, and an element $y$ of `G.J0s`, such that: the $\overline{\mathbb{Q}}$-point `gpts (σ • x - x)` equals $\operatorname{Spec}$ of the inclusion $Pl \hookrightarrow \overline{\mathbb{Q}}$ followed by $z$; the $k$-point `pts y` followed by the first projection from the $k$-base change of $D$ to $D.P$ equals $\operatorname{Spec} \pi_k$ followed by $z$; and `G.proj y = 0`, i.e. $y$ lies in the kernel `G.torus` of `G.proj`.
--
--   This is the instance for the Jacobian of $X_1(Mp)$, at a place above $p$ over $\mathbb{Q}(\zeta_p)$, of Grothendieck's result that inertia moves points of a semistable Jacobian into the toric part of the Néron special fibre: the displacement $\sigma x - x$ of an arbitrary class $x$ extends to a point of the relative $\operatorname{Pic}^0$ over the valuation ring $Pl$ whose reduction lies in the kernel of the projection to the Picard groups of the two components of the special fibre. It feeds the subsequent form of the statement used in the monodromy count behind the orthogonality of the toric and finite parts of $J_1(Mp)$ under the Weil pairing, and is deduced from the corresponding statement for differences of one-point divisor classes together with the description of the finite and toric parts of the special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_points_valuationSubring_and_proj_eq_zero_smul_sub_self_of_mem_inertia_of_curveModel_igusa_twoChartModel_x1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JOnePGeom
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JOnePOpsV2
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_WeilDatum
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

theorem ModularCurve.XOneP.exists_points_valuationSubring_and_proj_eq_zero_smul_sub_self_of_mem_inertia_of_curveModel_igusa_twoChartModel_x1_mul
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

    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j))
    (ε₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁) (ε₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂)
    (hε₁ : ε₁.1 ≫ i₁.1 = (sectionBaseChange k ε).1)

    (D : RelativePic0Designation A (ModularCurve.TwoChart.modelTo A (↥K) j))
    (hrep : Nonempty (RepresentsRelSubPic (ModularCurve.TwoChart.modelTo A (↥K) j) ε (algEquivZeroCut (ModularCurve.TwoChart.modelTo A (↥K) j) ε) D))
    (hsm : Smooth D.toBase) (hsep : IsSeparated D.toBase)

    (hreps : RepresentsRelSubPic (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (sectionBaseChange k ε)
      (algEquivZeroCut (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (sectionBaseChange k ε)) (D.baseChange k))
    (hPk : Nonempty (hreps.poincare.L ≅ (BaseChange.ofR (ModularCurve.TwoChart.modelTo A (↥K) j) ε k
      (hrep.some.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap A k), pullback.condition⟩)).L))
    (D₁ : RelativePic0Designation k c₁) (hrep₁ : Nonempty (RepresentsRelSubPic c₁ ε₁ (algEquivZeroCut c₁ ε₁) D₁))
    (D₂ : RelativePic0Designation k c₂) (hrep₂ : Nonempty (RepresentsRelSubPic c₂ ε₂ (algEquivZeroCut c₂ ε₂) D₂))

    (ν₂ : SchemeHomOver (D.baseChange k).toBase D₂.toBase)
    (hν₂ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t (D.baseChange k).toBase),
        Nonempty ((hrep₂.some.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a ν₂)).L ≅
          Scheme.Modules.rigidify (rigSection c₂ t ε₂) (pullback.snd c₂ t)
            ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj (hreps.poincare.pullbackAlong a).L)))

    [IsProper (ModularCurve.TwoChart.modelTo A (↥K) j)]

    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]

    (Mη : CurveModel (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p)))
    (eη : Mη.C ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) [IsIso eη]
    (heη : eη ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = Mη.toBase)

    [Mη_chart_nonempty : Nonempty (Scheme.Opens.toScheme ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)))]
    (hMηpin : ∀ a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
      ((Mη.ffEquiv.symm
          (Mη.C.germToFunctionField ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
            (((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
              (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))))
          : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((a : ↥K) : LaurentSeries L))

    (hgal : ∀ (g : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)),
      (∀ l : L, g (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l) →
      ∀ (x x' : {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // s ≫ Mη.toBase = 𝟙 _}),
      x'.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) =
        Spec.map (CommRingCat.ofHom (g : (AlgebraicClosure ℚ) →+* (AlgebraicClosure ℚ))) ≫ x.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) →
      Mη.pointEquivPlace x' =
        ModularCurve.arithmeticGalois (L := (AlgebraicClosure ℚ)) (ModularCurve.x1FunctionField (M * p)) g • Mη.pointEquivPlace x)

    (G : ModularCurve.JOneP.NeronSpecialFibreGeom p)
    (pts : G.J0s ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (D.baseChange k).toBase)
    (ptsI : G.JI ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D₁.toBase)
    (ptsE : G.JE ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D₂.toBase)
    (hadd : ∀ a b : G.J0s, Nonempty
      ((hreps.poincare.pullbackAlong (pts (a + b))).L ≅
        (hreps.poincare.pullbackAlong (pts a)).L ⊗ (hreps.poincare.pullbackAlong (pts b)).L))
    (haddI : ∀ a b : G.JI, Nonempty
      ((hrep₁.some.poincare.pullbackAlong (ptsI (a + b))).L ≅
        (hrep₁.some.poincare.pullbackAlong (ptsI a)).L ⊗ (hrep₁.some.poincare.pullbackAlong (ptsI b)).L))
    (haddE : ∀ a b : G.JE, Nonempty
      ((hrep₂.some.poincare.pullbackAlong (ptsE (a + b))).L ≅
        (hrep₂.some.poincare.pullbackAlong (ptsE a)).L ⊗ (hrep₂.some.poincare.pullbackAlong (ptsE b)).L))
    (hproj : ∀ x : G.J0s,
      ptsI (G.proj x).1 =
        postComp (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some) (pts x) ∧
      ptsE (G.proj x).2 = postComp ν₂ (pts x))

    (w : ModularCurve.IntegralWeightOneForm k M)
    (Mdl₁ : AlgebraicCurve.CurveModel k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) (e₁ : Mdl₁.C ≅ C₁)
    (he₁ : e₁.hom ≫ c₁ = Mdl₁.toBase)
    (Mdl₂ : AlgebraicCurve.CurveModel k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) (e₂ : Mdl₂.C ≅ C₂)
    (he₂ : e₂.hom ≫ c₂ = Mdl₂.toBase)

    (gpts : ModularCurve.JOne (M * p) ≃ SchemeHomOver (specMap A (AlgebraicClosure ℚ)) D.toBase)
    (hgadd : ∀ x y : ModularCurve.JOne (M * p), gpts (x + y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul _ (gpts x) (gpts y))

    (hDL : RepresentsRelSubPic (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (sectionBaseChange L ε)
        (algEquivZeroCut (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (sectionBaseChange L ε)) (D.baseChange L))
    (ajL : SchemeHomOver (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (D.baseChange L).toBase)
    (kL : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L))
    (ajbar : Mη.C ⟶ D.P)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
    (hPL : Nonempty (hDL.poincare.L ≅ (BaseChange.ofR (ModularCurve.TwoChart.modelTo A (↥K) j) ε L
      (hrep.some.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap A L), pullback.condition⟩)).L))
    (hajLε : (sectionBaseChange L ε).1 ≫ ajL.1 = (D.baseChange L).zeroSection)
    (hajL : (∀ (K' : Type) [Field K'] (t : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of L))
        (x : SchemeHomOver t (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L)),
      Nonempty ((hDL.poincare.pullbackAlong
          ⟨x.1 ≫ ajL.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajL.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (t ≫ (sectionBaseChange L ε).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange L ε).2).trans
              (Category.comp_id t)))).idealModule)))
    (hkL₁ : kL ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L) = pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)))
    (hkL₂ : kL ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L) = pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ≫ specMap L (AlgebraicClosure ℚ))
    (hajbar : ajbar = eη ≫ kL ≫ ajL.1 ≫ pullback.fst D.toBase (specMap A L))
    (hajbar_over : ajbar ≫ D.toBase = Mη.toBase ≫ specMap A (AlgebraicClosure ℚ))
    (hεbar : εbar.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = specMap A (AlgebraicClosure ℚ) ≫ ε.1)
    (hεbar_aj : εbar.1 ≫ ajbar = specMap A (AlgebraicClosure ℚ) ≫ D.zeroSection)
    (hpts_aj : (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      s.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = specMap A (AlgebraicClosure ℚ) ≫ ε.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ModularCurve.x1FunctionFieldBar (M * p)),
        (Dv : Divisor (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p))) =
          Finsupp.single (Mη.pointEquivPlace x) 1 - Finsupp.single (Mη.pointEquivPlace s) 1 ∧
        (gpts (Pic0.mk Dv)).1 = x.1 ≫ ajbar))

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))
    (πk : ↥Pl →+* k) (hAlgk : algebraMap A k = πk.comp ρ) (hπk : Function.Surjective πk) :
    ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ Pl.inertiaSubgroupIn ℚ → (∀ l : L, σ (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l) →
      ∀ x : ModularCurve.JOne (M * p),
        ∃ (z : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase) (y : G.J0s),
          (gpts (σ • x - x)).1 = Spec.map (CommRingCat.ofHom Pl.subtype) ≫ z.1 ∧
          (pts y).1 ≫ pullback.fst D.toBase (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ z.1 ∧ G.proj y = 0 := by sorry
