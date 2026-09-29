-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_heckeDivOneBar_single_eq_sum_and_red_eq_frob_inv_smul_of_gaussReduces_of_surjective_residue_igusaModel_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_heckeDivOneBar_single_eq_sum_and_red_eq_frob_inv_smul_of_gaussReduces_of_surjective_residue_igusaModel_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/8deedb5d-346d-5385-9292-124641871cde
-- title:
--   Uₚ at a place reducing into the Igusa component
-- statement:
--   Throughout, $p$ is a prime, $M$ a non-zero natural number with $5 \le M$ and $p \nmid M$, and $\bar{\mathbb Q} =$ `AlgebraicClosure ℚ`.
--
--   **Coefficient fields and the function field.** $L$ is a field of characteristic zero which is a $\{p\}$-cyclotomic extension of $\mathbb Q$, and $\zeta \in L$ is a primitive $p$-th root of unity. $K$ is an intermediate field of $L \subseteq L((q))$ subject to `hK`, which requires $K =$ `laurentBaseChange L (x1FunctionField (M * p))`, i.e. the subfield of $L((q))$ generated over $L$ by the coefficientwise image under `coeffEmb L` of the field `x1FunctionFieldC ℚ (M * p)` of $q$-expansions attached to $\Gamma_1(Mp)$. $A$ is a discrete valuation domain with an algebra structure over $L$ making $L$ its fraction field, such that $p$ lies in the maximal ideal of $A$ (`hAp`) and $\zeta$ is in the image of $A \to L$ (`hζA`); $K$ is an $A$-algebra compatibly with $A \to L \to K$. Finally $j \in K$ is an element, non-zero, whose Laurent expansion is `coeffEmb L jq` (`hj`), the image of the $q$-expansion $q^{-1}\cdot(\mathrm{jNumQ})$ of the modular invariant.
--
--   **The two-chart model and its special fibre.** `TwoChart.modelTo A K j` is the structure morphism over $\operatorname{Spec} A$ of the two-chart model `TwoChartModel A K j`, the pushout of the two affine charts $\operatorname{Spec}$ `chartAlgFin A K j` and $\operatorname{Spec}$ `chartAlgInf A K j`, where `chartAlgFin` (resp. `chartAlgInf`) is the $A$-subalgebra of $K$ of elements integral over $A[j]$ (resp. over $A[j^{-1}]$); this morphism is assumed proper. $k$ is an algebraically closed field of characteristic $p$ with an $A$-algebra structure. $C_1, C_2$ are schemes with morphisms $c_1, c_2$ to $\operatorname{Spec} k$, each proper, smooth of relative dimension $1$ and geometrically integral, and $i_1, i_2$ are morphisms over $k$ from $C_1$, $C_2$ to the special fibre `pullback (modelTo A K j) (specMap A k)` with its projection to $\operatorname{Spec} k$, both closed immersions. The hypothesis `hcover` requires every point of the special fibre to lie in the image of $i_1$ or of $i_2$; `hred` requires `pullback i₁.1 i₂.1` to be reduced, and `hn`, `hn0` require its underlying set to have cardinality $n$ with $0 < n$.
--
--   **The generic-fibre model over $\bar{\mathbb Q}$.** $\bar{\mathbb Q}$ carries $A$- and $L$-algebra structures forming a scalar tower. $M\eta$ is a `CurveModel` over $\bar{\mathbb Q}$ for the field `x1FunctionFieldBar (M * p)` $=$ `laurentBaseChange` $\bar{\mathbb Q}$ `(x1FunctionField (M * p))`: a proper smooth integral curve $M\eta.C \to \operatorname{Spec}\bar{\mathbb Q}$, a ring isomorphism `ffEquiv` of that field with the function field of $M\eta.C$ compatible with the structure morphism, and a bijection `placeOfPoint` from closed points to places, from which `pointEquivPlace` identifies $\bar{\mathbb Q}$-points over the base with places. The morphism $e\eta$ from $M\eta.C$ to `pullback (modelTo A K j) (specMap A` $\bar{\mathbb Q}$ `)` is an isomorphism and satisfies `heη`: $e\eta$ followed by the second projection equals $M\eta.\mathrm{toBase}$. Three compatibility hypotheses are imposed. `Mη_chart_nonempty`: the preimage, under $e\eta$ followed by the first projection, of the image open of the finite chart `TwoChart.ιFin A K j` is non-empty. `hMηpin` ($q$-expansion pin): for every $a$ in `chartAlgFin A K j`, the element of `x1FunctionFieldBar (M * p)` obtained by pulling $a$ back along $e\eta$ followed by the first projection, taking the germ at the generic point over that chart preimage, and transporting by `ffEquiv.symm`, has Laurent expansion `coeffMap (algebraMap L` $\bar{\mathbb Q}$ `)` applied to the expansion of $a$ in $L((q))$. `hgal` (Galois equivariance): for every $g \in \operatorname{Aut}_{\mathbb Q}(\bar{\mathbb Q})$ fixing the image of $L$ pointwise and for all $\bar{\mathbb Q}$-points $x, x'$ of $M\eta.C$ over the base, if $x'$ followed by $e\eta$ and the first projection equals $\operatorname{Spec}(g)$ followed by $x$, $e\eta$ and the first projection, then $M\eta.\mathrm{pointEquivPlace}\,x' = (\mathrm{arithmeticGalois}\ (\mathrm{x1FunctionField}\ (M * p))\,g) \cdot M\eta.\mathrm{pointEquivPlace}\,x$, the action being that of the coefficientwise semilinear automorphism attached to $g$.
--
--   **The Igusa component.** $w$ is an `IntegralWeightOneForm k M`: a weight-one modular form on $\Gamma_1(M)$ together with a power series over $\mathbb Z$ that is its integral $q$-expansion and whose image `intSeriesC k` in $k((q))$ is non-zero. The field `igusaFunctionFieldX1C k M w` is the subfield of $k((q))$ generated over $k$ by `x1FunctionFieldC k M` together with the inverse of that image. $\mathrm{Mdl}_1$ is a curve model over $k$ for this field, $e_1$ an isomorphism from $\mathrm{Mdl}_1.C$ to $C_1$ with `he₁`: $e_1.\mathrm{hom}$ followed by $c_1$ equals $\mathrm{Mdl}_1.\mathrm{toBase}$. Two compatibilities: `hne₁`, the preimage of the finite chart open under $e_1.\mathrm{hom}$ followed by $i_1$ and the first projection is non-empty; and `hgauss₁` (Gauss reading): for every $a$ in `chartAlgFin A K j` and all power series $x, y$ over $A$ with $\bar y \ne 0$ in $k[[q]]$, if $a \cdot y = x$ holds in $L((q))$ after applying $A \to L$ coefficientwise, then the element of `igusaFunctionFieldX1C k M w` obtained from $a$ by pull-back along $e_1.\mathrm{hom}$, $i_1$ and the first projection, germ at the generic point and `ffEquiv.symm`, has Laurent expansion $\bar x/\bar y$ in $k((q))$.
--
--   **Frobenius on the Igusa field.** $\mathrm{frobIg}$ is an element of `SemilinearAut k (igusaFunctionFieldX1C k M w)`, that is, a pair consisting of a ring automorphism of the Igusa field and one of $k$ compatible with the structure map, and `hfrobIg` requires each Laurent coefficient of $\mathrm{frobIg} \cdot x$ at index $n$ to be the $p$-th power of the $n$-th coefficient of $x$.
--
--   **Hecke data at level $Mp$ and prime $p$.** `hβdef` requires that `qExpand ℚ p y` lie in `x1x0FunctionFieldC ℚ (M * p) (M * p * p)` for every $y$ in `x1FunctionField (M * p)`; `hα` and `hβ` require the two $\bar{\mathbb Q}$-algebra maps `heckeAlphaOneBar` (the inclusion) and `heckeBetaOneBar` (given by $q \mapsto q^p$ under `hβdef`) from `laurentBaseChange` $\bar{\mathbb Q}$ `(x1FunctionField (M * p))` into `laurentBaseChange` $\bar{\mathbb Q}$ `(x1x0FunctionFieldC ℚ (M * p) (M * p * p))` to be integral ring homomorphisms; that larger field is assumed to have principal divisors over $\bar{\mathbb Q}$; and `hdeg` requires `finrankAlong` $\bar{\mathbb Q}$ `(heckeBetaOneBar` $\bar{\mathbb Q}$ `(M * p) p)` $= p$.
--
--   **The place of $\bar{\mathbb Q}$ above $p$ and the reduction map.** $Pl$ is a valuation subring of $\bar{\mathbb Q}$ with $p$ a non-unit in it (`hPl`), $\rho : A \to Pl$ a ring homomorphism lifting $A \to \bar{\mathbb Q}$ (`hρ`), $O$ a subring of $\bar{\mathbb Q}$ with $O \le Pl$ (`hO`) and $Pl \le O$ (`hOPl`), $\rho_O : A \to O$ lifting $A \to \bar{\mathbb Q}$ (`hρO`), and $\pi_k : Pl \to k$ a surjective ring homomorphism (`hπk`) with $A \to k$ equal to $\pi_k \circ \rho$ (`hAlgk`).
--
--   Finally, $\mathrm{red}_1$ is a map from places of `x1FunctionFieldBar (M * p)` over $\bar{\mathbb Q}$ to places of `igusaFunctionFieldX1C k M w` over $k$, and `hred₁` pins it down on geometrically reducing places: for every place $P$, every morphism $\xi$ from $\operatorname{Spec} O$ to the two-chart model lying over $\operatorname{Spec}(\rho_O)$, and every $k$-point $c$ of $C_1$ over the identity of $\operatorname{Spec} k$, if $\operatorname{Spec}(O \hookrightarrow \bar{\mathbb Q})$ followed by $\xi$ equals the $\bar{\mathbb Q}$-point `Mη.pointEquivPlace.symm P` followed by $e\eta$ and the first projection, and if $c$ followed by $i_1$ and the first projection equals $\operatorname{Spec}(\pi_k \circ (O \hookrightarrow Pl))$ followed by $\xi$, then $\mathrm{red}_1 P = \mathrm{Mdl}_1.\mathrm{pointEquivPlace}$ of the point $c$ transported along $e_1.\mathrm{inv}$.
--
--   **Conclusion.** For every place $P$ of `x1FunctionFieldBar (M * p)` over $\bar{\mathbb Q}$, assume there exist $\xi$ over $\operatorname{Spec}(\rho_O)$ and a $k$-point $c$ of $C_1$ such that: (a) $\operatorname{Spec}(O \hookrightarrow \bar{\mathbb Q})$ followed by $\xi$ is the $\bar{\mathbb Q}$-point of the model attached to $P$ through `Mη.pointEquivPlace.symm`, $e\eta$ and the first projection; (b) $c$ followed by $i_1$ and the first projection equals $\operatorname{Spec}(\pi_k \circ (O \hookrightarrow Pl))$ followed by $\xi$; (c) no point of the image of $c$ lies in the image of `pullback.fst i₁.1 i₂.1`; (d) every point of the image of $c$ followed by $i_1$ and the first projection lies in the image of the finite chart `TwoChart.ιFin A K j`.
--
--   Then there exists a family $Q : \mathrm{Fin}\,p \to$ places of `x1FunctionFieldBar (M * p)` over $\bar{\mathbb Q}$ such that both of the following hold. First, the divisor-level Hecke operator `heckeDivOneBar hα hβ`, namely pull-back along `heckeBetaOneBar` followed by push-forward along `heckeAlphaOneBar`, sends the divisor $\mathrm{single}\,P\,1$ to $\sum_{i : \mathrm{Fin}\,p} \mathrm{single}\,(Q\,i)\,1$. Second, for every $i$, the place $Q\,i$ again satisfies conditions (a)–(d) above (with $Q\,i$ in place of $P$, for some $\xi$ and $c$ depending on $i$), and $\mathrm{red}_1 (Q\,i) = \mathrm{frobIg}^{-1} \cdot \mathrm{red}_1 P$.
--
--   This is the place-level form of the Eichler–Shimura relation on the Igusa (Gauss) component of the special fibre of $X_1(Mp)$ at $p$: for a place of $\bar{\mathbb Q}(X_1(Mp))$ whose reduction lands on that component, away from the intersection with the other component and inside the finite $j$-chart, the level-$p$ Hecke correspondence $U_p = \alpha_*\beta^*$ breaks $[P]$ into $p$ degree-one places, each reducing to the inverse-Frobenius translate of the reduction of $P$. It feeds the subsequent statement combining this computation with the diamond and Atkin–Lehner twists on the same component.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_heckeDivOneBar_single_eq_sum_and_red_eq_frob_inv_smul_of_gaussReduces_of_surjective_residue_igusaModel_twoChartModel_x1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_FLTPrelim_Ramification
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
import Definitions.Def_ModularCurve_X1HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

theorem ModularCurve.XOneP.exists_heckeDivOneBar_single_eq_sum_and_red_eq_frob_inv_smul_of_gaussReduces_of_surjective_residue_igusaModel_twoChartModel_x1_mul
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

    (frobIg : SemilinearAut k ↥(ModularCurve.igusaFunctionFieldX1C k M w))
    (hfrobIg : ∀ (x : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) (n : ℤ),
      ((frobIg • x : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) : LaurentSeries k).coeff n = ((x : LaurentSeries k).coeff n) ^ p)

    (hβdef : ModularCurve.HeckeBetaOneDefined (M * p) p)
    (hα : ModularCurve.HeckeAlphaOneBarIntegral (AlgebraicClosure ℚ) (M * p) p)
    (hβ : ModularCurve.HeckeBetaOneBarIntegral (AlgebraicClosure ℚ) (M * p) p)
    [HasPrincipalDivisors (AlgebraicClosure ℚ)
      ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p)))]

    (hdeg : AlgebraicCurve.finrankAlong (AlgebraicClosure ℚ) (ModularCurve.heckeBetaOneBar (AlgebraicClosure ℚ) (M * p) p) = p)

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))
    (O : Subring (AlgebraicClosure ℚ)) (hO : O ≤ Pl.toSubring)
    (ρO : A →+* ↥O) (hρO : O.subtype.comp ρO = algebraMap A (AlgebraicClosure ℚ))
    (πk : ↥Pl →+* k) (hAlgk : algebraMap A k = πk.comp ρ)

    (hπk : Function.Surjective ⇑πk)

    (hOPl : Pl.toSubring ≤ O)

    (red₁ : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)) →
      AlgebraicCurve.Place k ↥(ModularCurve.igusaFunctionFieldX1C k M w))
    (hred₁ : ∀ (P : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)))
        (ξ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρO)) (ModularCurve.TwoChart.modelTo A (↥K) j))
        (c : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁),
      Spec.map (CommRingCat.ofHom O.subtype) ≫ ξ.1 =
        (Mη.pointEquivPlace.symm P).1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) →
      c.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
        Spec.map (CommRingCat.ofHom (πk.comp (Subring.inclusion hO))) ≫ ξ.1 →
      red₁ P = Mdl₁.pointEquivPlace ⟨c.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact c.2⟩) :

    ∀ (P : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p))),
      (∃ (ξ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρO)) (ModularCurve.TwoChart.modelTo A (↥K) j))
         (c : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁),
        Spec.map (CommRingCat.ofHom O.subtype) ≫ ξ.1 =
          (Mη.pointEquivPlace.symm P).1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ∧
        c.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
          Spec.map (CommRingCat.ofHom (πk.comp (Subring.inclusion hO))) ≫ ξ.1 ∧
        (∀ t, c.1.base t ∉ Set.range (pullback.fst i₁.1 i₂.1).base) ∧
        ∀ t, (c.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base t ∈
          Set.range (ModularCurve.TwoChart.ιFin A (↥K) j).base) →

      ∃ Q : Fin p → AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)),
        ModularCurve.heckeDivOneBar (L := AlgebraicClosure ℚ) (M := M * p) (ℓ := p) hα hβ (Finsupp.single P 1) =
          ∑ i : Fin p, Finsupp.single (Q i) 1 ∧
        ∀ i : Fin p,
          (∃ (ξ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρO)) (ModularCurve.TwoChart.modelTo A (↥K) j))
             (c : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁),
            Spec.map (CommRingCat.ofHom O.subtype) ≫ ξ.1 =
              (Mη.pointEquivPlace.symm (Q i)).1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ∧
            c.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
              Spec.map (CommRingCat.ofHom (πk.comp (Subring.inclusion hO))) ≫ ξ.1 ∧
            (∀ t, c.1.base t ∉ Set.range (pullback.fst i₁.1 i₂.1).base) ∧
            ∀ t, (c.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base t ∈
              Set.range (ModularCurve.TwoChart.ιFin A (↥K) j).base) ∧
          red₁ (Q i) = frobIg⁻¹ • red₁ P := by sorry
