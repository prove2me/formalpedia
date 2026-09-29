-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_representsRelSubPic_abelJacobi_pts_of_representsRelSubPic_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_representsRelSubPic_abelJacobi_pts_of_representsRelSubPic_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/237c7475-678a-5927-9a1f-d18c6fac0869
-- title:
--   Points dictionary and Abel–Jacobi map for X₁(Mp)'s relative Pic⁰
-- statement:
--   **Arithmetic data.** Fix a prime $p$ and an integer $M \ge 5$ with $p \nmid M$. Let $L$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of order $\{p\}$, and let $\zeta \in L$ be a primitive $p$-th root of unity. Let $K$ be an intermediate field of $L \subseteq \mathrm{LaurentSeries}\ L = L((q))$, assumed by `hK` to be [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), that is the $L$-subfield of $L((q))$ generated over $L$ by the image under coefficientwise extension of scalars [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) of the $q$-expansion function field [`ModularCurve.x1FunctionFieldC ℚ (M * p)`](def/ModularCurve_X1.html#L134) of $\Gamma_1(Mp)$ over $\mathbb{Q}$. Let $A$ be a domain which is a discrete valuation ring, equipped with an algebra map to $L$ realising $L$ as its fraction field, such that $p$ lies in the maximal ideal of $A$ (`hAp`) and $\zeta$ lies in the image of $A$ (`hζA`); $K$ carries an $A$-algebra structure compatible with $A \to L \to K$. Let $j \in K$ be non-zero with $q$-expansion [`ModularCurve.coeffEmb L ModularCurve.jq`](def/ModularCurve_LaurentCoeff.html#L81), the image in $L((q))$ of the $q$-expansion $q^{-1}\cdot(\text{numerator series of } j)$ of the modular invariant (`hj`).
--
--   **The model and its relative $\mathrm{Pic}^0$.** Write $c =$ [`ModularCurve.TwoChart.modelTo A (↥K) j`](def/ModularCurve_TwoChartModel.html#L252) for the structure morphism $\mathcal{X} \to \operatorname{Spec} A$ of the two-chart model, where $\mathcal{X} =$ [`ModularCurve.TwoChartModel A (↥K) j`](def/ModularCurve_TwoChartModel.html#L229) is the pushout of `fFin A (↥K) j` and `fInf A (↥K) j`, glueing the spectra of [`ModularCurve.TwoChart.chartAlgFin A (↥K) j`](def/ModularCurve_TwoChartModel.html#L135) (the elements of $K$ integral over $A[j]$) and of [`ModularCurve.TwoChart.chartAlgInf A (↥K) j`](def/ModularCurve_TwoChartModel.html#L137) (the elements integral over $A[j^{-1}]$), and $c$ is induced by the two structural algebra maps to $A$. Let $\varepsilon$ be a section of $c$ over $\operatorname{Spec} A$ (an element of `SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) c`, i.e. a morphism $\varepsilon_1 \colon \operatorname{Spec} A \to \mathcal{X}$ with $\varepsilon_1 \circ\!\!\!\circ\, c = \mathrm{id}$). Let $D$ be a `RelativePic0Designation A c`, i.e. a scheme $D.P$ together with a morphism $D.\mathrm{toBase}\colon D.P \to \operatorname{Spec} A$ and a section $D.\mathrm{zeroSection}$ of it. The hypothesis `hrep` asserts that the type `RepresentsRelSubPic c ε (algEquivZeroCut c ε) D` is non-empty: there exists a datum consisting of a rigidified line bundle `poincare` on $\mathcal{X} \times_{\operatorname{Spec} A} D.P$ satisfying the fibrewise condition `FibrewiseAlgEquivZero` (for every algebraically closed field $k$ and every $k$-point of the base, the restriction of the bundle to the corresponding fibre is algebraically equivalent to zero), such that for every $t \colon T \to \operatorname{Spec} A$ and every rigidified line bundle on $\mathcal{X}\times_{\operatorname{Spec}A} T$ satisfying that condition there is a unique morphism $T \to D.P$ over $\operatorname{Spec} A$ pulling `poincare` back to it up to isomorphism, and such that the pullback of `poincare` along the zero section is trivialised. Further hypotheses: $D.\mathrm{toBase}$ is smooth (`hsm`), and $c$ is proper.
--
--   **Generic fibre hypotheses.** The base change $\mathcal{X}_L =$ `baseChange A c L` $=$ `pullback.snd c (specMap A L)` is smooth of relative dimension $1$ (`hsmL`) and geometrically integral (`hgiL`); the base change `pullback.snd D.toBase (specMap A L)` of $D.\mathrm{toBase}$ to $L$ is proper (`hprL`) and geometrically connected (`hgcL`). Algebra structures on $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ over $A$ and over $L$, forming a tower, are fixed.
--
--   **The geometric model of the curve.** Let $M_\eta$ be a `CurveModel (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p))`: an integral scheme $M_\eta.C$, proper and smooth of relative dimension $1$ over $\operatorname{Spec} \overline{\mathbb{Q}}$, together with a ring isomorphism $M_\eta.\mathrm{ffEquiv}$ from [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) $=$ `laurentBaseChange (AlgebraicClosure ℚ) (x1FunctionField (M * p))` onto the function field of $M_\eta.C$ compatible with the structure maps, and a bijection from the closed points of $M_\eta.C$ onto the places of that field over $\overline{\mathbb{Q}}$, with the usual compatibilities (the ranges of the stalks are the valuation subrings, and every finite set of points lies in an affine open). Let $e_\eta \colon M_\eta.C \to \mathcal{X}\times_{\operatorname{Spec}A} \operatorname{Spec}\overline{\mathbb{Q}}$ be an isomorphism with $e_\eta$ followed by the projection to $\operatorname{Spec}\overline{\mathbb{Q}}$ equal to $M_\eta.\mathrm{toBase}$ (`heη`).
--
--   Two hypotheses pin $e_\eta$ down. First, the open subscheme of $M_\eta.C$ obtained as the preimage, under $e_\eta$ followed by `pullback.fst`, of the open image of the finite chart [`ModularCurve.TwoChart.ιFin A (↥K) j`](def/ModularCurve_TwoChartModel.html#L231) is non-empty (`Mη_chart_nonempty`). Secondly, `hMηpin` requires that for every $a$ in the finite chart algebra `chartAlgFin A (↥K) j`, the section of the structure sheaf of $\mathcal{X}\times_{\operatorname{Spec}A}\operatorname{Spec}\overline{\mathbb{Q}}$ over the image of the finite chart determined by $a$ (via the inverse of `Scheme.ΓSpecIso` and of the chart's `appIso`) pulls back along $e_\eta$ followed by `pullback.fst`, and its germ at the generic point, transported by $M_\eta.\mathrm{ffEquiv}^{-1}$ into `x1FunctionFieldBar (M * p)` $\subseteq \overline{\mathbb{Q}}((q))$, to the Laurent series obtained from the $q$-expansion of $a$ in $L((q))$ by applying [`ModularCurve.coeffMap`](def/ModularCurve_LaurentCoeff.html#L16) to the coefficients along $L \to \overline{\mathbb{Q}}$; thus $e_\eta$ is compatible with the $q$-expansion identification of the function field.
--
--   Thirdly, `hgal` is a Galois-equivariance hypothesis on $e_\eta$: for every $\mathbb{Q}$-algebra automorphism $g$ of $\overline{\mathbb{Q}}$ fixing the image of $L$ pointwise and all $\overline{\mathbb{Q}}$-points $x, x'$ of $M_\eta$ (sections of $M_\eta.\mathrm{toBase}$), if $x'$ followed by $e_\eta$ and `pullback.fst` equals $\operatorname{Spec}(g)$ followed by $x$ followed by $e_\eta$ and `pullback.fst`, then the place $M_\eta.\mathrm{pointEquivPlace}\ x'$ is the translate of $M_\eta.\mathrm{pointEquivPlace}\ x$ under the semilinear automorphism [`ModularCurve.arithmeticGalois (x1FunctionField (M * p)) g`](def/ModularCurve_ArithmeticGalois.html#L54), which acts on $\overline{\mathbb{Q}}((q))$ coefficientwise by $g$.
--
--   **Conclusion.** There exist
--
--   - a representability datum `hDL` of the same kind for the base change: a `RepresentsRelSubPic (baseChange A c L) (sectionBaseChange L ε) (algEquivZeroCut …) (D.baseChange L)`, where `D.baseChange L` has underlying scheme $D.P \times_{\operatorname{Spec}A} \operatorname{Spec} L$ with the induced zero section;
--
--   - a morphism $aj_L \colon \mathcal{X}_L \to (D.\mathrm{baseChange}\ L).P$ over $\operatorname{Spec} L$;
--
--   - a morphism $k_L \colon \mathcal{X}\times_{\operatorname{Spec}A}\operatorname{Spec}\overline{\mathbb{Q}} \to \mathcal{X}\times_{\operatorname{Spec}A}\operatorname{Spec}L$;
--
--   - a morphism $\overline{aj} \colon M_\eta.C \to D.P$;
--
--   - a $\overline{\mathbb{Q}}$-point $\overline{\varepsilon}$ of $M_\eta$ (a section of $M_\eta.\mathrm{toBase}$);
--
--   - a bijection $\mathrm{gpts}$ from [`ModularCurve.JOne (M * p)`](def/ModularCurve_X1.html#L186) $= \mathrm{Pic}^0(\overline{\mathbb{Q}},$ `x1FunctionFieldBar (M * p)` $)$, the group of degree-zero divisors (finitely supported $\mathbb{Z}$-valued functions on places) modulo principal divisors, onto the set of morphisms $\operatorname{Spec}\overline{\mathbb{Q}} \to D.P$ over $\operatorname{Spec} A$;
--
--   such that all of the following hold.
--
--   (1) The Poincaré bundle of `hDL` is isomorphic to `BaseChange.ofR c ε L` applied to the pullback of the Poincaré bundle of the chosen datum `hrep.some` along the first projection $D.P\times_{\operatorname{Spec}A}\operatorname{Spec}L \to D.P$.
--
--   (2) The section $\varepsilon_L =$ `sectionBaseChange L ε` followed by $aj_L$ is the zero section of `D.baseChange L`.
--
--   (3) For every field $K'$, every $t\colon \operatorname{Spec} K' \to \operatorname{Spec} L$ and every $K'$-point $x$ of $\mathcal{X}_L$ above $t$, the pullback of the Poincaré bundle of `hDL` along $x$ followed by $aj_L$ is isomorphic to the tensor product of the `lineBundle` of `RelEffCartierDiv.ofPoint` at $x$ — the dual of the ideal sheaf module of the graph of $x$ — with the `idealModule` of `RelEffCartierDiv.ofPoint` at $t$ followed by $\varepsilon_L$ — the ideal sheaf module of the graph of the cusp section; that is, $aj_L$ realises the Abel–Jacobi class of $x - \varepsilon_L$.
--
--   (4)–(5) $k_L$ is compatible with both projections: $k_L$ followed by `pullback.fst c (specMap A L)` is `pullback.fst c (specMap A ℚ̄)`, and $k_L$ followed by `pullback.snd c (specMap A L)` is `pullback.snd c (specMap A ℚ̄)` followed by `specMap L ℚ̄`.
--
--   (6) $\overline{aj}$ is the composite of $e_\eta$, $k_L$, $aj_L$ and the projection $D.P\times_{\operatorname{Spec}A}\operatorname{Spec}L \to D.P$.
--
--   (7) $\overline{aj}$ followed by $D.\mathrm{toBase}$ equals $M_\eta.\mathrm{toBase}$ followed by `specMap A ℚ̄`.
--
--   (8) $\overline{\varepsilon}$ is the cusp: $\overline{\varepsilon}$ followed by $e_\eta$ and `pullback.fst` equals `specMap A ℚ̄` followed by $\varepsilon_1$.
--
--   (9) $\overline{\varepsilon}$ followed by $\overline{aj}$ equals `specMap A ℚ̄` followed by $D.\mathrm{zeroSection}$.
--
--   (10) $\mathrm{gpts}$ is additive: for all $x, y \in$ `JOne (M * p)`, $\mathrm{gpts}(x+y)$ is the product of $\mathrm{gpts}(x)$ and $\mathrm{gpts}(y)$ for the relative group law `RepresentsRelSubPic.relativeGroupLaw` of `hrep.some` with respect to `algEquivZeroGroupCut`, evaluated at $\operatorname{Spec}\overline{\mathbb{Q}} \to \operatorname{Spec}A$.
--
--   (11) $\mathrm{gpts}$ is Galois-equivariant for automorphisms fixing $L$: for every $\mathbb{Q}$-algebra automorphism $\sigma$ of $\overline{\mathbb{Q}}$ fixing the image of $L$ pointwise and every $x \in$ `JOne (M * p)`, the morphism underlying $\mathrm{gpts}(\sigma \cdot x)$ equals $\operatorname{Spec}(\sigma)$ followed by the morphism underlying $\mathrm{gpts}(x)$.
--
--   (12) The dictionary matches $\overline{aj}$ on divisor classes of the form $[x]-[s]$: for all $\overline{\mathbb{Q}}$-points $x$ and $s$ of $M_\eta$ such that $s$ followed by $e_\eta$ and `pullback.fst` equals `specMap A ℚ̄` followed by $\varepsilon_1$, there is a degree-zero divisor $Dv$ on `x1FunctionFieldBar (M * p)` over $\overline{\mathbb{Q}}$ whose underlying divisor is $\delta_{v(x)} - \delta_{v(s)}$, where $v(\cdot) = M_\eta.\mathrm{pointEquivPlace}(\cdot)$, and such that the morphism underlying $\mathrm{gpts}$ of the class of $Dv$ equals $x$ followed by $\overline{aj}$.
--
--   This is the points dictionary, together with its Abel–Jacobi normalisation, for the relative $\mathrm{Pic}^0$ of the two-chart model of $X_1(Mp)$ over a discrete valuation ring $A$ with fraction field $\mathbb{Q}(\zeta_p)$ in which $p$ is not invertible: it transports $\mathrm{Pic}^0$ of $X_1(Mp)$ over $\overline{\mathbb{Q}}$, with its Galois action, onto the $\overline{\mathbb{Q}}$-points of the representing scheme, compatibly with the group law and with the Abel–Jacobi morphism defined on the generic fibre over $\mathbb{Q}(\zeta_p)$. It feeds the corresponding statement recording Hecke and Galois compatibilities for the same model, which is the form in which the Jacobian of $X_1(Mp)$ enters the modularity-lifting argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_representsRelSubPic_abelJacobi_pts_of_representsRelSubPic_twoChartModel_x1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

theorem ModularCurve.XOneP.exists_representsRelSubPic_abelJacobi_pts_of_representsRelSubPic_twoChartModel_x1_mul
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
    (hsm : Smooth D.toBase)

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
        ModularCurve.arithmeticGalois (L := (AlgebraicClosure ℚ)) (ModularCurve.x1FunctionField (M * p)) g • Mη.pointEquivPlace x) :
    ∃ (hDL : RepresentsRelSubPic (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (sectionBaseChange L ε)
          (algEquivZeroCut (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (sectionBaseChange L ε)) (D.baseChange L))
      (ajL : SchemeHomOver (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (D.baseChange L).toBase)
      (kL : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L))
      (ajbar : Mη.C ⟶ D.P)
      (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
      (gpts : ModularCurve.JOne (M * p) ≃ SchemeHomOver (specMap A (AlgebraicClosure ℚ)) D.toBase),

      Nonempty (hDL.poincare.L ≅ (BaseChange.ofR (ModularCurve.TwoChart.modelTo A (↥K) j) ε L
        (hrep.some.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap A L), pullback.condition⟩)).L) ∧

      (sectionBaseChange L ε).1 ≫ ajL.1 = (D.baseChange L).zeroSection ∧
      (∀ (K' : Type) [Field K'] (t : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of L))
          (x : SchemeHomOver t (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L)),
        Nonempty ((hDL.poincare.pullbackAlong
            ⟨x.1 ≫ ajL.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajL.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (t ≫ (sectionBaseChange L ε).1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange L ε).2).trans
                (Category.comp_id t)))).idealModule)) ∧

      kL ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L) = pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ∧
      kL ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L) = pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ≫ specMap L (AlgebraicClosure ℚ) ∧

      ajbar = eη ≫ kL ≫ ajL.1 ≫ pullback.fst D.toBase (specMap A L) ∧
      ajbar ≫ D.toBase = Mη.toBase ≫ specMap A (AlgebraicClosure ℚ) ∧
      εbar.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = specMap A (AlgebraicClosure ℚ) ≫ ε.1 ∧
      εbar.1 ≫ ajbar = specMap A (AlgebraicClosure ℚ) ≫ D.zeroSection ∧

      (∀ x y : ModularCurve.JOne (M * p),
        gpts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul _ (gpts x) (gpts y)) ∧

      (∀ (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)), (∀ l : L, σ (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l) →
        ∀ x : ModularCurve.JOne (M * p),
          (gpts (σ • x)).1 = Spec.map (CommRingCat.ofHom σ.toRingEquiv.toRingHom) ≫ (gpts x).1) ∧

      (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
        s.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = specMap A (AlgebraicClosure ℚ) ≫ ε.1 →
        ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ModularCurve.x1FunctionFieldBar (M * p)),
          (Dv : Divisor (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p))) =
            Finsupp.single (Mη.pointEquivPlace x) 1 - Finsupp.single (Mη.pointEquivPlace s) 1 ∧
          (gpts (Pic0.mk Dv)).1 = x.1 ≫ ajbar) := by sorry
