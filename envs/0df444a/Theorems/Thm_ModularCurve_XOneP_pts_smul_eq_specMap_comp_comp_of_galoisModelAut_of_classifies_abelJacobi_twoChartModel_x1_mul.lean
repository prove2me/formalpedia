-- Prove2me | Theorems.Thm_ModularCurve_XOneP_pts_smul_eq_specMap_comp_comp_of_galoisModelAut_of_classifies_abelJacobi_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.pts_smul_eq_specMap_comp_comp_of_galoisModelAut_of_classifies_abelJacobi_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/d6cf175b-4df1-5688-8088-280fbad54e3b
-- title:
--   Galois transport of J₁(Mp)-points by the Picard automorphism N
-- statement:
--   Throughout, `SchemeHomOver g f` denotes the type of scheme morphisms $\varphi$ with $\varphi$ followed by $f$ equal to $g$, and a `RelativePic0Designation` over a ring consists of a scheme `D.P`, a structure morphism `D.toBase` to the spectrum of that ring, and a section `D.zeroSection` of it.
--
--   **Arithmetic data.** A prime $p$, a natural number $M$ with $M \ge 5$ and $p \nmid M$, a field $L$ of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of type $\{p\}$, an element $\zeta \in L$ that is a primitive $p$-th root of unity, and an intermediate field $K$ of $L \subseteq \mathrm{LaurentSeries}(L)$ with `hK` asserting $K =$ [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), the subfield of $L((q))$ generated over $L$ by the coefficientwise image of the function field of $X_1(Mp)$ over $\mathbb{Q}$. Further, a discrete valuation domain $A$ with fraction field $L$ such that $p$ lies in the maximal ideal of $A$ (`hAp`) and $\zeta$ is in the image of $A$ (`hζA`), together with an $A$-algebra structure on $K$ compatible with $A \to L \to K$, and an element $j \in K$ whose Laurent expansion is the coefficientwise image [`ModularCurve.coeffEmb L ModularCurve.jq`](def/ModularCurve_LaurentCoeff.html#L81) of the $q$-expansion of $j$ (`hj`), with $j \neq 0$.
--
--   **The model and its rigidified relative $\mathrm{Pic}^0$.** A section $\varepsilon$ of the structure morphism [`ModularCurve.TwoChart.modelTo A ↥K j`](def/ModularCurve_TwoChartModel.html#L252) of the two-chart model [`ModularCurve.TwoChartModel A ↥K j`](def/ModularCurve_TwoChartModel.html#L229) over $\operatorname{Spec} A$; a designation $D$ as above for that structure morphism; the hypothesis `hrep`, that the type `RepresentsRelSubPic` for the model, $\varepsilon$, the cut `algEquivZeroCut` and $D$ is non-empty, i.e. $D$ carries a Poincaré rigidified line bundle lying in the cut, every $\varepsilon$-rigidified line bundle on a base change of the model whose geometric fibres are algebraically equivalent to zero is classified by a unique morphism to `D.toBase`, and the zero section classifies the unit bundle; and the hypotheses `hsm`, `hsep` that `D.toBase` is smooth and separated. The structure morphism of the model is assumed proper.
--
--   **Base change to $L$ and to $\overline{\mathbb{Q}}$.** Algebra structures making $A \to L \to \mathrm{AlgebraicClosure}\ \mathbb{Q}$ a tower. The hypotheses `hsmL`, `hgiL` state that the base change of the model to $L$ is smooth of relative dimension $1$ and geometrically integral; `hprL`, `hgcL` that the second projection of the pullback of `D.toBase` along $\operatorname{Spec} L \to \operatorname{Spec} A$ is proper and geometrically connected. The hypothesis `hDL` states that the $L$-base changed model, with the base-changed section `sectionBaseChange L ε`, the corresponding cut and `D.baseChange L`, again represents the rigidified relative $\mathrm{Pic}^0$; `hPL` asserts that the Poincaré bundle of `hDL` is isomorphic to the bundle obtained by `BaseChange.ofR` from the pull-back of the Poincaré bundle of `hrep.some` along the first projection of the pullback of `D.toBase` along $\operatorname{Spec} L \to \operatorname{Spec} A$.
--
--   **The geometric curve and its pinning.** A `CurveModel` $M\eta$ over $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ of the field [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) (a proper integral scheme, smooth of relative dimension $1$ over the base, together with an identification of its function field, a bijection between its closed points and the places of that field, and the attendant compatibilities); an isomorphism $e\eta$ from `Mη.C` to the pullback of the model along $\operatorname{Spec} \overline{\mathbb{Q}} \to \operatorname{Spec} A$, with `heη` saying that $e\eta$ followed by the second projection is `Mη.toBase`; non-emptiness of the open subscheme of `Mη.C` obtained as the preimage, under $e\eta$ followed by the first projection, of the image of the finite chart [`ModularCurve.TwoChart.ιFin A ↥K j`](def/ModularCurve_TwoChartModel.html#L231). The pinning hypothesis `hMηpin` says that for every element $a$ of the finite-chart algebra [`ModularCurve.TwoChart.chartAlgFin A ↥K j`](def/ModularCurve_TwoChartModel.html#L135), the function-field element of `x1FunctionFieldBar (M * p)` obtained by transporting $a$ through the chart, along $e\eta$ followed by the first projection, to the germ at the generic point and back through `Mη.ffEquiv` has Laurent expansion equal to the coefficientwise image of the expansion of $a$ under $L \to \overline{\mathbb{Q}}$.
--
--   The hypothesis `hgal` is a Galois-equivariance statement for the place dictionary: for every $g \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ fixing the image of $L$ pointwise and all $\overline{\mathbb{Q}}$-points $x, x'$ of `Mη.C` over the base, if $x'$ followed by $e\eta$ and the first projection equals $\operatorname{Spec}(g)$ followed by $x$, $e\eta$ and the first projection, then `Mη.pointEquivPlace x'` is the image of `Mη.pointEquivPlace x` under the action of [`ModularCurve.arithmeticGalois (x1FunctionField (M * p)) g`](def/ModularCurve_ArithmeticGalois.html#L54), the semilinear automorphism given by applying $g$ coefficientwise.
--
--   **Hecke inputs.** `hin : ModularCurve.HeckeDiamondInputsAll (M * p)` and `hcomm : ModularCurve.HeckeDiamondCommuteBar (M * p)`, the commutation of the generators $T_\ell$ and $\langle d \rangle$ in the bar setting.
--
--   **Galois action on $A$.** A `MulSemiringAction` of $L \simeq_{\mathbb{Q}} L$ on $A$, with `hΓA` requiring $\operatorname{alg}(s \cdot a) = s(\operatorname{alg}(a))$ for all $s$ and $a$.
--
--   **The dictionary and its Abel–Jacobi normalisation.** A bijection `gpts` from [`ModularCurve.JOne (M * p)`](def/ModularCurve_X1.html#L186) (the degree-zero divisor class group $\mathrm{Pic}^0$ of `x1FunctionFieldBar (M * p)`) onto the $\overline{\mathbb{Q}}$-points of `D.toBase`, which by `hgadd` carries addition to the relative group law `RepresentsRelSubPic.relativeGroupLaw` of `hrep.some` for the group cut `algEquivZeroGroupCut`. The remaining data pin down `gpts` as an Abel–Jacobi map: a morphism `ajL` from the $L$-base changed model to `(D.baseChange L).toBase` over that model, a morphism `kL` from the pullback over $\overline{\mathbb{Q}}$ to the pullback over $L$, a morphism `ajbar : Mη.C ⟶ D.P`, and a $\overline{\mathbb{Q}}$-point $\bar\varepsilon$ of `Mη.C`, subject to: `hajLε`, the base-changed $\varepsilon$ followed by `ajL` is the zero section of `D.baseChange L`; `hajL`, for every field $K'$, every $t : \operatorname{Spec} K' \to \operatorname{Spec} L$ and every $K'$-point $x$ of the $L$-base changed model over $t$, the pull-back of the Poincaré bundle of `hDL` along $x$ followed by `ajL` is isomorphic to the tensor product of the line bundle (the dual of the ideal sheaf module) of the relative effective Cartier divisor `RelEffCartierDiv.ofPoint` at $x$ with the ideal sheaf module of `RelEffCartierDiv.ofPoint` at $t$ followed by the base-changed $\varepsilon$, that is to $\mathcal{O}(x - \varepsilon)$; `hkL₁` and `hkL₂`, that `kL` is compatible with the two projections, the second up to $\operatorname{Spec} \overline{\mathbb{Q}} \to \operatorname{Spec} L$; `hajbar`, that `ajbar` is $e\eta$ followed by `kL`, by `ajL` and by the first projection of the pullback of `D.toBase` along $\operatorname{Spec} L \to \operatorname{Spec} A$; `hajbar_over`, that `ajbar` followed by `D.toBase` equals `Mη.toBase` followed by $\operatorname{Spec} \overline{\mathbb{Q}} \to \operatorname{Spec} A$; `hεbar`, that $\bar\varepsilon$ followed by $e\eta$ and the first projection equals $\operatorname{Spec} \overline{\mathbb{Q}} \to \operatorname{Spec} A$ followed by $\varepsilon$; `hεbar_aj`, that $\bar\varepsilon$ followed by `ajbar` equals $\operatorname{Spec} \overline{\mathbb{Q}} \to \operatorname{Spec} A$ followed by `D.zeroSection`; and `hpts_aj`, that for all $\overline{\mathbb{Q}}$-points $x, s$ of `Mη.C` with $s$ pinned to $\varepsilon$ in the sense of `hεbar`, there is a degree-zero divisor $D_v$ of `x1FunctionFieldBar (M * p)` whose underlying finitely supported function is $[\,$`Mη.pointEquivPlace x`$\,] - [\,$`Mη.pointEquivPlace s`$\,]$ and such that the morphism underlying `gpts (Pic0.mk Dv)` is $x$ followed by `ajbar`.
--
--   **The Galois model automorphism and its Picard transport.** A fixed $s \in L \simeq_{\mathbb{Q}} L$; a morphism `ws` of the two-chart model to itself with `hws`: `ws` followed by the structure morphism equals the structure morphism followed by $\operatorname{Spec}$ of the action of $s$ on $A$; a ring automorphism $\rho_s$ of the finite-chart algebra with `hρs`: the Laurent expansion of $\rho_s(b)$ is the coefficientwise image under $s$ of that of $b$; `hwρ`: the finite chart followed by `ws` equals $\operatorname{Spec}(\rho_s)$ followed by the finite chart; and `hsinv`: $\operatorname{Spec}$ of the action of $s^{-1}$ followed by $\operatorname{Spec}$ of the action of $s$ is the identity of $\operatorname{Spec} A$. Finally, a morphism $N$ from `D.P` to itself over `D.toBase` followed by $\operatorname{Spec}$ of the action of $s^{-1}$, together with `hN`: for every scheme $T$, every $t : T \to \operatorname{Spec} A$ and every point $a$ of `D.toBase` over $t$, the pull-back of the Poincaré bundle of `hrep.some` along $a$ followed by $N$ (a point over $t$ followed by $\operatorname{Spec}(s^{-1})$) is isomorphic to the rigidification `Scheme.Modules.rigidify`, along the rigidifying section `rigSection` and the second projection, of the pull-back along the map of pullbacks induced by `ws`, the identity of $T$ and $\operatorname{Spec}$ of the action of $s$, of the pull-back of the Poincaré bundle along $a$.
--
--   **Conclusion.** With the `HeckeAlgOne`-module structure [`ModularCurve.heckeModuleOneBar (M * p)`](def/ModularCurve_X1HeckeModule.html#L129) on [`ModularCurve.JOne (M * p)`](def/ModularCurve_X1.html#L186) in force, for every $\sigma' \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ such that $\sigma'(\operatorname{alg}_{L \to \overline{\mathbb{Q}}}(l)) = \operatorname{alg}_{L \to \overline{\mathbb{Q}}}(s\,l)$ for all $l \in L$, and every $x \in$ [`ModularCurve.JOne (M * p)`](def/ModularCurve_X1.html#L186), the morphism underlying `gpts (σ' • x)` equals $\operatorname{Spec}$ of $\sigma'$ followed by the morphism underlying `gpts x` and then by $N$.
--
--   This is the pinned form of the Galois-equivariance law for the identification of $J_1(Mp)(\overline{\mathbb{Q}})$ with the $\overline{\mathbb{Q}}$-points of the scheme representing the rigidified relative $\mathrm{Pic}^0$ of the two-chart integral model of $X_1(Mp)$ over $\mathbb{Z}_{(p)}[\zeta_p]$: the arithmetic Galois action on divisor classes is transported by the Picard pull-back along the model automorphism covering $\operatorname{Spec}(s)$. It is used by the corresponding existence statement for such a transport and by the statement identifying the transport morphism uniquely through its action on rigidified line bundles, which together give the Galois action on the Jacobian in the integral model used for level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_pts_smul_eq_specMap_comp_comp_of_galoisModelAut_of_classifies_abelJacobi_twoChartModel_x1_mul.lean

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
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JOnePOpsV2
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

theorem ModularCurve.XOneP.pts_smul_eq_specMap_comp_comp_of_galoisModelAut_of_classifies_abelJacobi_twoChartModel_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j))
    (D : RelativePic0Designation A (ModularCurve.TwoChart.modelTo A (↥K) j))
    (hrep : Nonempty (RepresentsRelSubPic (ModularCurve.TwoChart.modelTo A (↥K) j) ε (algEquivZeroCut (ModularCurve.TwoChart.modelTo A (↥K) j) ε) D))
    (hsm : Smooth D.toBase) (hsep : IsSeparated D.toBase)

    [IsProper (ModularCurve.TwoChart.modelTo A (↥K) j)]

    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]

    (hsmL : SmoothOfRelativeDimension 1 (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L))
    (hgiL : GeometricallyIntegral (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L))

    (hprL : IsProper (pullback.snd D.toBase (specMap A L)))
    (hgcL : GeometricallyConnected (pullback.snd D.toBase (specMap A L)))

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
    (hin : ModularCurve.HeckeDiamondInputsAll (M * p)) (hcomm : ModularCurve.HeckeDiamondCommuteBar (M * p))

    [MulSemiringAction (L ≃ₐ[ℚ] L) A]
    (hΓA : ∀ (s : L ≃ₐ[ℚ] L) (a : A), algebraMap A L (s • a) = s (algebraMap A L a))

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

    (s : L ≃ₐ[ℚ] L)
    (ws : ModularCurve.TwoChartModel A (↥K) j ⟶ ModularCurve.TwoChartModel A (↥K) j)
    (hws : ws ≫ (ModularCurve.TwoChart.modelTo A (↥K) j) = (ModularCurve.TwoChart.modelTo A (↥K) j) ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s))))
    (ρs : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ≃+* ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))
    (hρs : ∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
      (((ρs b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) : ↥K) : LaurentSeries L) =
        ModularCurve.coeffMap (s.toAlgHom.toRingHom) (((b : ↥K)) : LaurentSeries L))
    (hwρ : ModularCurve.TwoChart.ιFin A (↥K) j ≫ ws = Spec.map (CommRingCat.ofHom ρs.toRingHom) ≫ ModularCurve.TwoChart.ιFin A (↥K) j)

    (hsinv : (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s⁻¹))) ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s))) = 𝟙 (Spec (CommRingCat.of A)))

    (N : SchemeHomOver (D.toBase ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s⁻¹)))) D.toBase)
    (hN : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of A)) (a : SchemeHomOver t D.toBase),
      Nonempty ((hrep.some.poincare.pullbackAlong
          (⟨a.1 ≫ N.1, by rw [Category.assoc, N.2, ← Category.assoc, a.2]⟩ : SchemeHomOver (t ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s⁻¹)))) D.toBase)).L ≅
        Scheme.Modules.rigidify (rigSection (ModularCurve.TwoChart.modelTo A (↥K) j) (t ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s⁻¹)))) ε) (pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (t ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s⁻¹)))))
          ((Scheme.Modules.pullback
              (pullback.map (ModularCurve.TwoChart.modelTo A (↥K) j) (t ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s⁻¹)))) (ModularCurve.TwoChart.modelTo A (↥K) j) t ws (𝟙 T) (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s)))
                hws.symm (by rw [Category.assoc, hsinv, Category.comp_id, Category.id_comp]))).obj
            (hrep.some.poincare.pullbackAlong a).L))) :
    letI := ModularCurve.heckeModuleOneBar (M * p)
    ∀ (σ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      (∀ l : L, σ' (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) (s l)) →
      ∀ x : ModularCurve.JOne (M * p),
        (gpts (σ' • x)).1 = Spec.map (CommRingCat.ofHom σ'.toRingEquiv.toRingHom) ≫ (gpts x).1 ≫ N.1 := by sorry
