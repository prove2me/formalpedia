-- Prove2me | Theorems.Thm_ModularCurve_XOneP_addEquiv_proj_fst_eq_frob_smul_of_pts_eq_frobenius_comp_of_gaussReading_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.addEquiv_proj_fst_eq_frob_smul_of_pts_eq_frobenius_comp_of_gaussReading_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/6de9c7a4-a2a0-59b6-ade2-437bf4fa6634
-- title:
--   Frobenius twist on the Igusa component is coefficientwise
-- statement:
--   Arithmetic frame. Let $p$ be a prime, let $M$ be a non-zero natural number with $5 \le M$ and $p \nmid M$, let $L$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of type $\{p\}$, and let $\zeta \in L$ be a primitive $p$-th root of unity. Let $K$ be an intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ with $K =$ [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), i.e. $K$ is generated over $L$ by the coefficientwise images of the $X_1(Mp)$ function field inside $L((q))$. Let $A$ be a discrete valuation domain with fraction field $L$, with $p$ in the maximal ideal of $A$ and with $\zeta$ in the image of $A \to L$, and let $K$ be an $A$-algebra compatibly with the tower $A \to L \to K$. Let $j \in K$ be an element whose Laurent series is the coefficientwise image of the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157), and $j \ne 0$. Let $k$ be an algebraically closed field of characteristic $p$ which is an $A$-algebra. Write $\mathfrak{X} \to \operatorname{Spec} A$ for the two-chart model [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252) (the pushout of the spectra of the two chart algebras `chartAlgFin` and `chartAlgInf` attached to $j$), and $\mathfrak{X}_k =$ `baseChange A (ModularCurve.TwoChart.modelTo A K j) k` for its base change along $A \to k$.
--
--   Geometric special fibre. Let $C_1, C_2$ be schemes with morphisms $c_1 : C_1 \to \operatorname{Spec} k$, $c_2 : C_2 \to \operatorname{Spec} k$ which are proper, smooth of relative dimension $1$ and geometrically integral, and let $i_1, i_2$ be closed immersions of $C_1$, $C_2$ into $\mathfrak{X}_k$ over $\operatorname{Spec} k$. The hypothesis `hcover` requires that every point of the pullback of $\mathfrak{X} \to \operatorname{Spec} A$ along $\operatorname{Spec} k \to \operatorname{Spec} A$ lies in the image of $i_1$ or of $i_2$; `hred` requires the scheme-theoretic intersection `pullback i₁.1 i₂.1` to be reduced; and `hn`, `hn0` require that the number of its points is a natural number $n$ with $0 < n$.
--
--   Sections and $\mathrm{Pic}^0$ data. Let $\varepsilon$ be a section of $\mathfrak{X} \to \operatorname{Spec} A$ and let $\varepsilon_1$, $\varepsilon_2$ be $k$-sections of $c_1$, $c_2$, with $\varepsilon_1$ followed by $i_1$ equal to the base-changed section `sectionBaseChange k ε` (hypothesis `hε₁`). Let $D$ be a relative $\mathrm{Pic}^0$ designation for $\mathfrak{X} \to \operatorname{Spec} A$, that is a scheme $D.P$ with a structure morphism `D.toBase` to $\operatorname{Spec} A$ together with a zero section; `hrep` asserts that $D$ represents, via a Poincaré rigidified line bundle, the sub-Picard functor cut out by the fibrewise algebraic triviality condition `algEquivZeroCut` for $(\mathfrak{X}, \varepsilon)$, and `hsm`, `hsep` require `D.toBase` to be smooth and separated. The hypothesis `hreps` provides such a representability datum for the base change $D.\mathrm{baseChange}\,k$ relative to $(\mathfrak{X}_k, \mathrm{sectionBaseChange}\,k\,\varepsilon)$, and `hPk` requires its Poincaré bundle to be isomorphic to the bundle obtained from the Poincaré bundle of `hrep.some` by pulling back along the first projection of $D.\mathrm{toBase} \times_{\operatorname{Spec} A} \operatorname{Spec} k$ and descending by `BaseChange.ofR`. Let $D_1$, $D_2$ be relative $\mathrm{Pic}^0$ designations for $c_1$, $c_2$ over $k$, with representability data `hrep₁`, `hrep₂` for the corresponding `algEquivZeroCut` conditions.
--
--   Restriction to $C_2$. Let $\nu_2$ be a morphism $(D.\mathrm{baseChange}\,k).P \to D_2.P$ over $\operatorname{Spec} k$; the hypothesis `hν₂` requires that for every $k$-scheme $t : T \to \operatorname{Spec} k$ and every $T$-point $a$ of $(D.\mathrm{baseChange}\,k).\mathrm{toBase}$, the pullback of the Poincaré bundle of `hrep₂.some` along $a$ followed by $\nu_2$ is isomorphic to the rigidification, with respect to the section `rigSection c₂ t ε₂` and the projection `pullback.snd c₂ t`, of the pullback along `curveChange i₂` of the pullback of the Poincaré bundle of `hreps` along $a$.
--
--   Raynaud dictionaries. Let $G$ be a datum of type [`ModularCurve.JOneP.NeronSpecialFibreGeom p`](def/ModularCurve_JOnePGeom.html#L9): abelian groups $G.J_{0s}$, $G.J_I$, $G.J_E$, a subgroup `G.torus` of $G.J_{0s}$, and a surjective homomorphism $G.\mathrm{proj} : G.J_{0s} \to G.J_I \times G.J_E$ with kernel `G.torus`. Let `pts`, `ptsI`, `ptsE` be bijections of $G.J_{0s}$, $G.J_I$, $G.J_E$ with the sets of $k$-sections of $(D.\mathrm{baseChange}\,k).\mathrm{toBase}$, $D_1.\mathrm{toBase}$, $D_2.\mathrm{toBase}$ respectively. The hypotheses `hadd`, `haddI`, `haddE` require each of the three bijections to be additive at the level of Poincaré bundles: the pullback of the relevant Poincaré bundle at $a + b$ is isomorphic to the tensor product of the pullbacks at $a$ and at $b$. The hypothesis `hproj` requires, for every $x \in G.J_{0s}$, that `ptsI (G.proj x).1` is `pts x` post-composed with the pullback morphism `RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some`, and that `ptsE (G.proj x).2` is `pts x` post-composed with $\nu_2$.
--
--   Igusa identification of $C_1$ and the Gauss reading. Let $w$ be an integral weight-one form of level $M$ over $k$ (a weight-one modular form on $\Gamma_1(M)$ together with an integral $q$-expansion `series` whose reduction `intSeriesC k` is non-zero), and write $\mathrm{Ig} =$ [`ModularCurve.igusaFunctionFieldX1C k M w`](def/ModularCurve_IgusaFunctionFieldX1.html#L35) for the associated Igusa function field inside $k((q))$. Let $\mathrm{Mdl}_1$ be a curve model over $k$ of $\mathrm{Ig}$ (a proper smooth integral curve with a specified isomorphism `ffEquiv` of $\mathrm{Ig}$ with its function field and a bijection of its closed points with the places of $\mathrm{Ig}$), let $e_1 : \mathrm{Mdl}_1.C \cong C_1$ be an isomorphism of schemes with $e_1$ followed by $c_1$ equal to $\mathrm{Mdl}_1.\mathrm{toBase}$ (hypothesis `he₁`), and let `hne₁` require the preimage, under $e_1$ followed by $i_1$ followed by the first projection of $\mathfrak{X} \times_{\operatorname{Spec} A} \operatorname{Spec} k$, of the image open set of the finite chart [`ModularCurve.TwoChart.ιFin A K j`](def/ModularCurve_TwoChartModel.html#L231) to be non-empty. The hypothesis `hgauss₁` is the Gauss reading: for every element $a$ of the finite chart algebra `chartAlgFin A K j` and all power series $x, y$ over $A$ such that the image of $y$ in $k[[q]]$ is non-zero and such that $a \cdot y = x$ holds in $L((q))$ (the Laurent series of $a$ times the image of $y$ equals the image of $x$), the function on $\mathrm{Mdl}_1.C$ obtained from $a$ by transporting along the chart isomorphism, pulling back along $e_1$ followed by $i_1$ followed by the first projection, taking the germ at the generic point and carrying it into $\mathrm{Ig}$ by $\mathrm{Mdl}_1.\mathrm{ffEquiv}^{-1}$, has Laurent series over $k$ equal to the quotient of the image of $x$ by the image of $y$ in $k((q))$.
--
--   Abel–Jacobi pin and Frobenius normalisation. Let $\theta_1 : G.J_I \simeq \mathrm{Pic}^0(k, \mathrm{Ig})$ be an additive equivalence, where $\mathrm{Pic}^0$ is the quotient of the group of degree-zero divisors (finitely supported $\mathbb{Z}$-valued functions on the places of $\mathrm{Ig}$ over $k$) by the principal ones. The hypothesis `hθpin₁` requires: for every $g \in G.J_I$ and every $k$-section $x$ of $c_1$, if the pullback of the Poincaré bundle of `hrep₁.some` along `ptsI g` is isomorphic to the line bundle of the relative effective Cartier divisor of the point $x$ tensored with the ideal module of the relative effective Cartier divisor of $\varepsilon_1$, then there is a degree-zero divisor $Dv$ on $\mathrm{Ig}$ equal to the difference of the delta functions at the places corresponding, under $\mathrm{Mdl}_1.\mathrm{pointEquivPlace}$, to $x$ followed by $e_1^{-1}$ and to $\varepsilon_1$ followed by $e_1^{-1}$, with $\theta_1 g = \mathrm{Pic}^0\text{-class of } Dv$. Finally let $\mathrm{frobIg}$ be a semilinear automorphism of $\mathrm{Ig}$ over $k$ (a pair consisting of a ring automorphism of $\mathrm{Ig}$ and one of $k$ which are compatible with the structure map), subject to `hfrobIg`: for every $x \in \mathrm{Ig}$ and every $n \in \mathbb{Z}$, the $n$-th coefficient of the Laurent series of $\mathrm{frobIg} \cdot x$ is the $p$-th power of the $n$-th coefficient of that of $x$.
--
--   Conclusion. For all $y, y' \in G.J_{0s}$: if the $k$-point of $D.P$ obtained from `pts y'` followed by the first projection $D.\mathrm{toBase} \times_{\operatorname{Spec} A} \operatorname{Spec} k \to D.P$ equals $\operatorname{Spec}$ of the $p$-power Frobenius endomorphism `frobenius k p` of $k$ followed by the corresponding $k$-point attached to $y$, then
--   $$\theta_1\bigl((G.\mathrm{proj}\,y').1\bigr) = \mathrm{frobIg} \cdot \theta_1\bigl((G.\mathrm{proj}\,y).1\bigr),$$
--   an identity in $\mathrm{Pic}^0(k, \mathrm{Ig})$ with $\mathrm{frobIg}$ acting through the semilinear action on divisor classes.
--
--   This is the special-fibre half of the Frobenius pin for the Néron special fibre of $J_1(Mp)$ at $p$: under the Gauss-pinned identification of the cusp component of the special fibre with a smooth proper model of the Igusa function field, the arithmetic Frobenius twist of a $k$-point of the $\mathrm{Pic}^0$-scheme corresponds, on the Igusa factor $J_I$, to the coefficientwise $p$-th power map on $q$-expansions. It is used in the treatment of the norm-free part of $J_1(Mp)$, in particular in the statements about the pairing and the Frobenius action on the $\mathrm{Pic}^0$-pair attached to the Igusa specialisation data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_addEquiv_proj_fst_eq_frob_smul_of_pts_eq_frobenius_comp_of_gaussReading_twoChartModel_x1_mul.lean

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
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

theorem ModularCurve.XOneP.addEquiv_proj_fst_eq_frob_smul_of_pts_eq_frobenius_comp_of_gaussReading_twoChartModel_x1_mul
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

    [hne₁ : Nonempty (Scheme.Opens.toScheme ((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)))]
    (hgauss₁ : ∀ (a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) (x y : PowerSeries A),
      y.map (algebraMap A k) ≠ 0 →
      ((a : ↥K) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L)) =
        HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
      ((Mdl₁.ffEquiv.symm
          (Mdl₁.C.germToFunctionField ((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
            (((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
              (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))))
          : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) : LaurentSeries k) =
        HahnSeries.ofPowerSeries ℤ k (x.map (algebraMap A k)) / HahnSeries.ofPowerSeries ℤ k (y.map (algebraMap A k)))

    (θ₁ : G.JI ≃+ AlgebraicCurve.Pic0 k ↥(ModularCurve.igusaFunctionFieldX1C k M w))
    (hθpin₁ : ∀ (g : G.JI) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁),
      Nonempty ((hrep₁.some.poincare.pullbackAlong (ptsI g)).L ≅
        (RelEffCartierDiv.ofPoint c₁ x.1 x.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint c₁ ε₁.1 ε₁.2).idealModule) →
      ∃ Dv : Divisor.degZero (K := k) (F := ↥(ModularCurve.igusaFunctionFieldX1C k M w)),
        (Dv : Divisor k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) =
          Finsupp.single (Mdl₁.pointEquivPlace ⟨x.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact x.2⟩) 1 -
            Finsupp.single (Mdl₁.pointEquivPlace ⟨ε₁.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact ε₁.2⟩) 1 ∧
        θ₁ g = Pic0.mk Dv)

    (frobIg : SemilinearAut k ↥(ModularCurve.igusaFunctionFieldX1C k M w))
    (hfrobIg : ∀ (x : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) (n : ℤ),
      ((frobIg • x : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) : LaurentSeries k).coeff n = ((x : LaurentSeries k).coeff n) ^ p) :

    ∀ (y y' : G.J0s),
      (pts y').1 ≫ pullback.fst D.toBase (specMap A k) =
        Spec.map (CommRingCat.ofHom (frobenius k p)) ≫ (pts y).1 ≫ pullback.fst D.toBase (specMap A k) →
      θ₁ (G.proj y').1 = frobIg • θ₁ (G.proj y).1 := by sorry
