-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_isClosedImmersion_isProper_smooth_normFreePart_of_representsRelSubPic_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_isClosedImmersion_isProper_smooth_normFreePart_of_representsRelSubPic_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/89bb68ac-56af-5724-be80-0b83a3ef5801
-- title:
--   Abelian subscheme of relative Pic⁰ cutting out the norm-free part
-- statement:
--   **Arithmetic setting.** Let $p$ be a prime and $M$ a nonzero natural number with $5 \le M$ (`hM`) and $p \nmid M$ (`hpM`). Let $L$ be a field of characteristic zero which is a $\{p\}$-cyclotomic extension of $\mathbb{Q}$, and let $\zeta \in L$ be a primitive $p$-th root of unity. Let $K$ be an intermediate field of $L \subseteq L((q))$ (`LaurentSeries L`) which, by `hK`, equals [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), i.e. the subfield of $L((q))$ generated over $L$ by the $q$-expansions of the function field of $X_1(Mp)$ over $\mathbb{Q}$. Let $A$ be a discrete valuation domain with fraction field $L$, with $p$ in the maximal ideal of $A$ (`hAp`) and with $\zeta$ in the image of $A \to L$ (`hζA`), and let $A$ act on $K$ compatibly with $A \to L \to K$. Let $j \in K$ be the element whose $q$-expansion is the image under [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) (`hj`), assumed nonzero. Write $X =$ [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252) for the resulting two-chart model $X \to \operatorname{Spec} A$, glued from the affine charts attached to the subalgebras [`ModularCurve.TwoChart.chartAlgFin A K j`](def/ModularCurve_TwoChartModel.html#L135) and its counterpart at infinity, and let $\varepsilon$ be a section of $X \to \operatorname{Spec} A$ (a `SchemeHomOver (𝟙 (Spec (CommRingCat.of A)))`). The morphism $X \to \operatorname{Spec} A$ is assumed proper.
--
--   **Relative Picard data.** Let $D$ be a `RelativePic0Designation` for $X \to \operatorname{Spec} A$, that is a scheme `D.P` with a structure morphism `D.toBase` to $\operatorname{Spec} A$ together with a zero section. The hypothesis `hrep` asserts that $D$ represents, in the sense of `RepresentsRelSubPic`, the functor of $\varepsilon$-rigidified line bundles on $X/A$ satisfying the condition `algEquivZeroCut`, namely those whose restriction to every geometric fibre is algebraically equivalent to zero: there is a Poincaré rigidified bundle over `D.toBase` satisfying this condition, every such bundle over a base $T$ is induced by a unique $T$-point of `D.toBase`, and the Poincaré bundle is trivial along the zero section. Further, `D.toBase` is smooth (`hsm`) and separated (`hsep`). Over $L$ and over $\overline{\mathbb{Q}}$ (with $A \to L \to \overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` a tower of algebras) it is assumed that the base change $X_L \to \operatorname{Spec} L$ is smooth of relative dimension $1$ (`hsmL`) and geometrically integral (`hgiL`), and that $D_L =$ `pullback.snd D.toBase (specMap A L)` is proper (`hprL`) and geometrically connected (`hgcL`).
--
--   **Geometric curve model and its pinning.** Let $M\eta$ be a `CurveModel` over $\overline{\mathbb{Q}}$ with function field [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182) — a proper integral scheme, smooth of relative dimension $1$ over $\overline{\mathbb{Q}}$, together with an isomorphism of its function field with `x1FunctionFieldBar (M * p)` compatible with the base, and a bijection between its closed points and the places of that function field. Let $e\eta$ be an isomorphism from `Mη.C` to $X \times_{\operatorname{Spec} A} \operatorname{Spec} \overline{\mathbb{Q}}$ commuting with the structure morphisms (`heη`). The preimage under $e\eta$ followed by the first projection of the finite chart of $X$ is assumed nonempty (`Mη_chart_nonempty`), and `hMηpin` pins the identification $q$-expansion by $q$-expansion: for every $a$ in `chartAlgFin A K j`, the element of `x1FunctionFieldBar (M * p)` obtained by restricting $a$ along $e\eta$ followed by the first projection, taking its germ at the generic point of `Mη.C` and transporting it by `Mη.ffEquiv.symm`, has $q$-expansion equal to the image of the $q$-expansion of $a$ under [`ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ))`](def/ModularCurve_LaurentCoeff.html#L16). The hypothesis `hgal` is the Galois equivariance of this dictionary: for every automorphism $g$ of $\overline{\mathbb{Q}}$ over $\mathbb{Q}$ fixing $L$ pointwise and all $\overline{\mathbb{Q}}$-points $x, x'$ of `Mη.C` over $\overline{\mathbb{Q}}$ such that $x'$ followed by $e\eta$ and the first projection equals $\operatorname{Spec}(g)$ followed by $x$ followed by $e\eta$ and the first projection, the place attached to $x'$ is the translate of the place attached to $x$ by [`ModularCurve.arithmeticGalois (x1FunctionField (M * p)) g`](def/ModularCurve_ArithmeticGalois.html#L54).
--
--   **Hecke and diamond inputs.** `hin` is [`ModularCurve.HeckeDiamondInputsAll (M * p)`](def/ModularCurve_X1HeckeModule.html#L58): for every prime $\ell$ the predicate `HeckeInputsOneAlong (AlgebraicClosure ℚ) (M * p) ℓ` holds, and for every $d$ coprime to $M p$ there exist a $\mathbb{Q}$-automorphism $\sigma$ of `x1FunctionField (M * p)` with `IsDiamondAut (M * p) d σ` and a $\overline{\mathbb{Q}}$-automorphism $\sigma'$ of `x1FunctionFieldBar (M * p)` which is a base change of `diamondAut (M * p) d`. `hcomm` is [`ModularCurve.HeckeDiamondCommuteBar (M * p)`](def/ModularCurve_X1HeckeModule.html#L54): the generators `heckeDiamondGenBar (M * p) i` commute pairwise. Together these make [`ModularCurve.heckeModuleOneBar (M * p)`](def/ModularCurve_X1HeckeModule.html#L129) a module structure of [`ModularCurve.HeckeAlgOne = MvPolynomial (Nat.Primes ⊕ ℕ) ℤ`](def/ModularCurve_X1HeckeModule.html#L16) on $J_1(Mp) =$ [`ModularCurve.JOne (M * p)`](def/ModularCurve_X1.html#L186), the group `Pic0` of degree-zero divisor classes of `x1FunctionFieldBar (M * p)` over $\overline{\mathbb{Q}}$. In addition, $\operatorname{Gal}(L/\mathbb{Q})$ acts on $A$ by ring automorphisms, compatibly with $A \to L$ (`hΓA`).
--
--   **Points dictionary and operator layer.** Let `gpts` be a bijection from $J_1(Mp)$ to the $\overline{\mathbb{Q}}$-points of `D.toBase` over $\operatorname{Spec} A$, additive for the relative group law `RepresentsRelSubPic.relativeGroupLaw` of `hrep.some` with respect to the group condition `algEquivZeroGroupCut` (`hgadd`). Let $\varphi$ assign to each $t \in$ `HeckeAlgOne` an endomorphism of `D.P` over $\operatorname{Spec} A$, and let $\tau$ assign to each $s \in \operatorname{Gal}(L/\mathbb{Q})$ a morphism `D.P ⟶ D.P` whose composite with `D.toBase` is `D.toBase` followed by $\operatorname{Spec}$ of the ring automorphism of $A$ determined by $s$. The compatibilities are: each $\varphi(t)$ is additive on $T$-points for the relative group law (`hφmul`); `gpts (t • x)` is `gpts x` followed by $\varphi(t)$ (`hφpts`); $\tau(1)$ is the identity of `D.P` and $\tau(s s')$ is $\tau(s)$ followed by $\tau(s')$ (`hτ1`, `hτmul`); $\tau(s)$ and $\varphi(t)$ commute (`hτφ`); and, for $\sigma'$ an automorphism of $\overline{\mathbb{Q}}$ over $\mathbb{Q}$ restricting on $L$ to $s$, `gpts (σ' • x)` equals $\operatorname{Spec}(\sigma')$ followed by `gpts x` followed by $\tau(s^{-1})$ (`hτpts`).
--
--   **Abel–Jacobi data.** `hDL` asserts that `D.baseChange L` represents the corresponding rigidified relative Picard condition for $X_L/L$ with the base-changed section `sectionBaseChange L ε`. Let `ajL` be a morphism $X_L \to (D.baseChange L)$`.P` over $\operatorname{Spec} L$, let `kL` be a morphism $X \times_A \overline{\mathbb{Q}} \to X \times_A L$ compatible with the two projections (`hkL₁`, `hkL₂`), and let `ajbar : Mη.C ⟶ D.P` and `εbar` a $\overline{\mathbb{Q}}$-point of `Mη.C`. The hypothesis `hPL` provides an isomorphism between the Poincaré bundle of `hDL` and the base change to $L$ (`BaseChange.ofR`) of the Poincaré bundle of `hrep.some` pulled back along the first projection of $D_L$. The morphism `ajL` sends the cusp section to the zero section (`hajLε`), and `hajL` is its defining property: for every field $K'$, every $t : \operatorname{Spec} K' \to \operatorname{Spec} L$ and every $K'$-point $x$ of $X_L$ over $t$, the pullback of the Poincaré bundle of `hDL` along $x$ followed by `ajL` is isomorphic to the tensor product of the `lineBundle` (the dual of the ideal sheaf module) of the relative effective Cartier divisor of the point $x$ with the `idealModule` of the relative effective Cartier divisor of the cusp point $t$ followed by `sectionBaseChange L ε`; that is, to $\mathcal{O}(x - \varepsilon)$. Finally `hajbar` identifies `ajbar` with $e\eta$ followed by `kL`, `ajL` and the first projection of $D_L$, `hajbar_over` states that `ajbar` lies over `Mη.toBase` followed by `specMap A (AlgebraicClosure ℚ)`, `hεbar` states that `εbar` is the cusp point (its composite with $e\eta$ and the first projection is `specMap A (AlgebraicClosure ℚ)` followed by $\varepsilon$), `hεbar_aj` states that `εbar` followed by `ajbar` is the zero section base-changed to $\overline{\mathbb{Q}}$, and `hpts_aj` states that for all $\overline{\mathbb{Q}}$-points $x$ and $s$ of `Mη.C` with $s$ the cusp point there is a degree-zero divisor $Dv$ of `x1FunctionFieldBar (M * p)` equal, as a finitely supported function on places, to the difference of the single divisors attached to the places of $x$ and of $s$, and such that `gpts (Pic0.mk Dv)` is $x$ followed by `ajbar`.
--
--   **Conclusion.** There exist a scheme $\mathcal{A}$, a morphism $a : \mathcal{A} \to \operatorname{Spec} A$ and a morphism $\iota : \mathcal{A} \to$ `D.P` over $\operatorname{Spec} A$ such that:
--
--   1. $\iota$ is a closed immersion;
--
--   2. $a$ is proper and smooth, and for every algebraically closed field $k$ and every morphism $s : \operatorname{Spec} k \to \operatorname{Spec} A$ the fibre product `pullback a s` is a connected topological space;
--
--   3. for every scheme $T$ and every $s : T \to \operatorname{Spec} A$: the unit $T$-point of the relative group law of `hrep.some` factors through $\iota$, i.e. there is a $T$-point $o$ of $a$ with $o$ followed by $\iota$ equal to that unit; for all $T$-points $x, y$ of $a$ there is a $T$-point $z$ of $a$ with $z$ followed by $\iota$ equal to the product, under the relative group law, of $x$ followed by $\iota$ and $y$ followed by $\iota$; and for every $T$-point $x$ of $a$ there is a $T$-point $z$ of $a$ with $z$ followed by $\iota$ equal to the inverse, under the relative group law, of $x$ followed by $\iota$;
--
--   4. for every $x \in J_1(Mp)$, $x$ lies in [`ModularCurve.normFreePartAt (M * p) p`](def/ModularCurve_X1PrimitiveSpecializationAtP.html#L29) — by definition the range of the additive endomorphism `normFreeEnd (M * p) (normFreeRepsAt (M * p) p)` of $J_1(Mp)$ — if and only if there is a $\overline{\mathbb{Q}}$-point $y$ of $a$ over $\operatorname{Spec} A$ with $y$ followed by $\iota$ equal to `gpts x`;
--
--   5. for every $t \in$ `HeckeAlgOne`, every scheme $T$, every $s : T \to \operatorname{Spec} A$ and every $T$-point $x$ of $a$, there is a $T$-point $z$ of $a$ with $z$ followed by $\iota$ equal to $x$ followed by $\iota$ and then by $\varphi(t)$.
--
--   This is the good-reduction statement for the norm-free part of $J_1(Mp)$ in the form used along the level-lowering route: inside the relative $\mathrm{Pic}^0$ of the two-chart model of $X_1(Mp)$ over a discrete valuation ring containing $\zeta_p$ and $p$, the norm-free part is cut out by a closed subscheme which is proper and smooth over the base with connected geometric fibres, is closed under the relative group law, and is stable under the Hecke–diamond operators. It is used by [`ModularCurve.exists_qExpSemistableSpecializationPinnedV3_family_normFreePart_and_diamond_of_dvd_of_not_sq_dvd_of_le_div`](thm.html#ModularCurve.exists_qExpSemistableSpecializationPinnedV3_family_normFreePart_and_diamond_of_dvd_of_not_sq_dvd_of_le_div), where properness supplies integral points of the norm-free part over valuation rings of $\overline{\mathbb{Q}}$ above $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_isClosedImmersion_isProper_smooth_normFreePart_of_representsRelSubPic_twoChartModel_x1_mul.lean

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
import Definitions.Def_ModularCurve_X1PrimitiveSpecializationAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

theorem ModularCurve.XOneP.exists_isClosedImmersion_isProper_smooth_normFreePart_of_representsRelSubPic_twoChartModel_x1_mul
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
    (φ : ModularCurve.HeckeAlgOne → SchemeHomOver D.toBase D.toBase)
    (τ : ∀ s : L ≃ₐ[ℚ] L,
      SchemeHomOver (D.toBase ≫ Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s))) D.toBase)
    (hφmul : ∀ (t : ModularCurve.HeckeAlgOne) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of A)) (x y : SchemeHomOver s D.toBase),
      NeronModelInfra.schemeHomOverComp ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul s x y) (φ t) =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul s
          (NeronModelInfra.schemeHomOverComp x (φ t)) (NeronModelInfra.schemeHomOverComp y (φ t)))
    (hφpts : letI := ModularCurve.heckeModuleOneBar (M * p)
      ∀ (t : ModularCurve.HeckeAlgOne) (x : ModularCurve.JOne (M * p)), (gpts (t • x)).1 = (gpts x).1 ≫ (φ t).1)
    (hτ1 : (τ 1).1 = 𝟙 D.P) (hτmul : ∀ s s' : L ≃ₐ[ℚ] L, (τ (s * s')).1 = (τ s).1 ≫ (τ s').1)
    (hτφ : ∀ (t : ModularCurve.HeckeAlgOne) (s : L ≃ₐ[ℚ] L), (τ s).1 ≫ (φ t).1 = (φ t).1 ≫ (τ s).1)

    (hgadd : ∀ x y : ModularCurve.JOne (M * p), gpts (x + y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul _ (gpts x) (gpts y))
    (hτpts : ∀ (σ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (s : L ≃ₐ[ℚ] L),
      (∀ l : L, σ' (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) (s l)) →
      ∀ x : ModularCurve.JOne (M * p),
        (gpts (σ' • x)).1 = Spec.map (CommRingCat.ofHom σ'.toRingEquiv.toRingHom) ≫ (gpts x).1 ≫ (τ s⁻¹).1)

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
        (gpts (Pic0.mk Dv)).1 = x.1 ≫ ajbar)) :
    ∃ (𝒜 : Scheme.{0}) (a : 𝒜 ⟶ Spec (CommRingCat.of A)) (ι : SchemeHomOver a D.toBase),

      IsClosedImmersion ι.1 ∧

      IsProper a ∧ Smooth a ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)),
        ConnectedSpace ↥(pullback a s)) ∧

      (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of A)),
        (∃ o : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp o ι =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).one s) ∧
        (∀ x y : SchemeHomOver s a, ∃ z : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp z ι =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul s
            (NeronModelInfra.schemeHomOverComp x ι) (NeronModelInfra.schemeHomOverComp y ι)) ∧
        (∀ x : SchemeHomOver s a, ∃ z : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp z ι =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).inv s
            (NeronModelInfra.schemeHomOverComp x ι))) ∧

      (∀ x : ModularCurve.JOne (M * p),
        x ∈ ModularCurve.normFreePartAt (M * p) p ↔
          ∃ y : SchemeHomOver (specMap A (AlgebraicClosure ℚ)) a, y.1 ≫ ι.1 = (gpts x).1) ∧

      (∀ (t : ModularCurve.HeckeAlgOne) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of A)) (x : SchemeHomOver s a),
        ∃ z : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp z ι =
          NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp x ι) (φ t)) := by sorry
