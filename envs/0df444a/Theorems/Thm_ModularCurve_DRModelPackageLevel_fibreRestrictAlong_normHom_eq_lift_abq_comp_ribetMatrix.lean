-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_fibreRestrictAlong_normHom_eq_lift_abq_comp_ribetMatrix
-- name    : ModularCurve.DRModelPackageLevel.fibreRestrictAlong_normHom_eq_lift_abq_comp_ribetMatrix
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/9c9d428e-4acb-5377-b678-01eafb64d09e
-- title:
--   Ribet's matrix as an identity of morphisms on special fibres
-- statement:
--   Fix $N_0 \ge 1$ and a prime $p$ with $p \nmid N_0$, and let $\mathfrak P$ be a `DRModelPackageLevel` for $N_0, p$ over $R =$ `R p`. Assume the degeneracy morphism $\mathfrak P.\pi$ and its twist $\mathfrak P.\pi_w$ are finite, flat and locally of finite presentation of constant fibre rank $p+1$. Let $D$, with datum `hD`, represent the functor of line bundles on the model, rigidified along $\mathfrak P.\varepsilon_{\inf}$ and fibrewise algebraically equivalent to zero, and let $\varepsilon_0$, $D_0$, `hD₀` do the same for the level-$N_0$ model `toBase0`. Let $\delta_0,\delta_1 \colon D \to D_0$ be morphisms over $\operatorname{Spec} R$ which, for every base point $a$, send the Poincaré bundle to the rigidified norm module of degree $p+1$ (the $(p+1)$-st determinant of the pushforward, twisted by the dual of that of the unit) along the base change of $\mathfrak P.\pi$, respectively $\mathfrak P.\pi_w$. Let $\kappa$ be an algebraically closed field of characteristic $p$ over $R$, with representability data `hDκ`, `hD₀κ` for the base-changed designations and compatibility isomorphisms `hPκ`, `hP₀κ` of the Poincaré bundles with the base changes of those over $R$. Let $\mathrm{abq}_0,\mathrm{abq}_1 \colon D_\kappa \to (D_0)_\kappa$ classify, instead, the plain pullbacks along the two component maps $\mathfrak P.\mathrm{comp}\ \kappa\ i$ of the special fibre, let $\varphi_\kappa = \mathfrak P.\mathrm{comp}\ \kappa\ 1$ followed by the fibre map of $\mathfrak P.\pi$, assumed finite, flat, locally of finite presentation of rank $p$ and compatible with the base structure morphism, and let $F$ be the endomorphism of $(D_0)_\kappa$ classifying the norm module of degree $p$ along $\varphi_\kappa$. Assume $D$ is smooth and $D_0$ proper over $R$. Write $\cdot$ for the relative group law on $(D_0)_\kappa$ obtained by base change from that on $D_0$, let $M \colon (D_0)_\kappa \times_\kappa (D_0)_\kappa \to (D_0)_\kappa \times_\kappa (D_0)_\kappa$ have components $(x,y) \mapsto x \cdot F(y)$ and $(x,y) \mapsto F(x) \cdot y$ on the universal pair of points, and let $q = (\mathrm{abq}_0,\mathrm{abq}_1) \colon D_\kappa \to (D_0)_\kappa \times_\kappa (D_0)_\kappa$. Then the restriction of $\delta_i$ to the fibres over $\operatorname{Spec}\kappa$ equals $q$ followed by $M$ followed by the $i$-th projection, for $i = 0, 1$.
--
--   This is the scheme-theoretic form of Ribet's matrix $\begin{pmatrix} 1 & F \\ F & 1\end{pmatrix}$ computing the two degeneracy maps on the special fibre of the Jacobian of the Deligne–Rapoport model at $p$, where $\pi$ is the identity on one component of the special fibre and the Frobenius-related norm on the other. It strengthens the corresponding identity on $\kappa$-points to an identity of morphisms, and is used in the analysis of the kernel of the induced map on special fibres.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_fibreRestrictAlong_normHom_eq_lift_abq_comp_ribetMatrix.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_NeronSpecialFibreRestriction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve ModularCurve.DRLevel
open AlgebraicGeometry

theorem ModularCurve.DRModelPackageLevel.fibreRestrictAlong_normHom_eq_lift_abq_comp_ribetMatrix
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)

    [IsFinite 𝔓.π.1] [Flat 𝔓.π.1] [LocallyOfFinitePresentation 𝔓.π.1] (hrk : ∀ x, 𝔓.π.1.finrank x = p + 1)

    (D : RelativePic0Designation (R p) (toBase N₀ p))
    (hD : RepresentsRelSubPic (toBase N₀ p) 𝔓.εinf (algEquivZeroCut (toBase N₀ p) 𝔓.εinf) D)
    (ε₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R p)))) (toBase0 N₀ p))
    (D₀ : RelativePic0Designation (R p) (toBase0 N₀ p))
    (hD₀ : RepresentsRelSubPic (toBase0 N₀ p) ε₀ (algEquivZeroCut (toBase0 N₀ p) ε₀) D₀)

    [IsFinite 𝔓.πw.1] [Flat 𝔓.πw.1] [LocallyOfFinitePresentation 𝔓.πw.1] (hrk_w : ∀ x, 𝔓.πw.1.finrank x = p + 1)

    (δ : Fin 2 → SchemeHomOver D.toBase D₀.toBase)
    (hδ₀ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (a : SchemeHomOver t D.toBase),
      Nonempty ((hD₀.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a (δ 0))).L ≅
        Scheme.Modules.rigidify (rigSection (toBase0 N₀ p) t ε₀) (pullback.snd (toBase0 N₀ p) t)
          (Scheme.Modules.normModule (curveChange 𝔓.π.1 𝔓.π.2 t) (p + 1) (hD.poincare.pullbackAlong a).L)))
    (hδ₁ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (a : SchemeHomOver t D.toBase),
      Nonempty ((hD₀.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a (δ 1))).L ≅
        Scheme.Modules.rigidify (rigSection (toBase0 N₀ p) t ε₀) (pullback.snd (toBase0 N₀ p) t)
          (Scheme.Modules.normModule (curveChange 𝔓.πw.1 𝔓.πw.2 t) (p + 1) (hD.poincare.pullbackAlong a).L)))

    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] [Algebra (R p) κ]
    (hDκ : RepresentsRelSubPic (baseChange (R p) (toBase N₀ p) κ) (sectionBaseChange κ 𝔓.εinf)
      (algEquivZeroCut (baseChange (R p) (toBase N₀ p) κ) (sectionBaseChange κ 𝔓.εinf)) (D.baseChange κ))
    (hPκ : Nonempty (hDκ.poincare.L ≅ (BaseChange.ofR (toBase N₀ p) 𝔓.εinf κ
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) κ), pullback.condition⟩)).L))
    (hD₀κ : RepresentsRelSubPic (baseChange (R p) (toBase0 N₀ p) κ) (sectionBaseChange κ ε₀)
      (algEquivZeroCut (baseChange (R p) (toBase0 N₀ p) κ) (sectionBaseChange κ ε₀)) (D₀.baseChange κ))
    (hP₀κ : Nonempty (hD₀κ.poincare.L ≅ (BaseChange.ofR (toBase0 N₀ p) ε₀ κ
        (hD₀.poincare.pullbackAlong ⟨pullback.fst D₀.toBase (specMap (R p) κ), pullback.condition⟩)).L))

    (abq : Fin 2 → SchemeHomOver (D.baseChange κ).toBase (D₀.baseChange κ).toBase)
    (habq : ∀ (i : Fin 2) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of κ)) (a : SchemeHomOver t (D.baseChange κ).toBase),
      Nonempty ((hD₀κ.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a (abq i))).L ≅
        Scheme.Modules.rigidify (rigSection (baseChange (R p) (toBase0 N₀ p) κ) t (sectionBaseChange κ ε₀))
            (pullback.snd (baseChange (R p) (toBase0 N₀ p) κ) t)
          ((Scheme.Modules.pullback (curveChange (𝔓.comp κ (algebraMap (R p) κ) i) (𝔓.comp_over κ (algebraMap (R p) κ) i) t)).obj
            (hDκ.poincare.pullbackAlong a).L)))

    (φκ : fibre0 (N₀ := N₀) (algebraMap (R p) κ) ⟶ fibre0 (N₀ := N₀) (algebraMap (R p) κ))
    (hφκ : φκ = 𝔓.comp κ (algebraMap (R p) κ) 1 ≫ fibreMap0 𝔓.π (algebraMap (R p) κ))
    (hφκ_over : φκ ≫ baseChange (R p) (toBase0 N₀ p) κ = baseChange (R p) (toBase0 N₀ p) κ)
    [IsFinite φκ] [Flat φκ] [LocallyOfFinitePresentation φκ] (hφ_rk : ∀ x, φκ.finrank x = p)

    (F : SchemeHomOver (D₀.baseChange κ).toBase (D₀.baseChange κ).toBase)
    (hF : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of κ)) (b : SchemeHomOver t (D₀.baseChange κ).toBase),
      Nonempty ((hD₀κ.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp b F)).L ≅
        Scheme.Modules.rigidify (rigSection (baseChange (R p) (toBase0 N₀ p) κ) t (sectionBaseChange κ ε₀))
            (pullback.snd (baseChange (R p) (toBase0 N₀ p) κ) t)
          (Scheme.Modules.normModule (curveChange φκ hφκ_over t) p (hD₀κ.poincare.pullbackAlong b).L)))

    (hsm : Smooth D.toBase) (hpr₀ : IsProper D₀.toBase) :
    let strB : (D₀.baseChange κ).P ⟶ Spec (CommRingCat.of κ) := (D₀.baseChange κ).toBase
    let lawB := (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).baseChange (specMap (R p) κ)
    let tBB : pullback strB strB ⟶ Spec (CommRingCat.of κ) := pullback.fst strB strB ≫ strB
    let xBB : SchemeHomOver tBB strB := ⟨pullback.fst strB strB, rfl⟩
    let yBB : SchemeHomOver tBB strB := ⟨pullback.snd strB strB, pullback.condition.symm⟩
    let m₀ := lawB.mul tBB xBB (NeronModelInfra.schemeHomOverComp yBB F)
    let m₁ := lawB.mul tBB (NeronModelInfra.schemeHomOverComp xBB F) yBB
    let Mx : pullback strB strB ⟶ pullback strB strB := pullback.lift m₀.1 m₁.1 (m₀.2.trans m₁.2.symm)
    let q : (D.baseChange κ).P ⟶ pullback strB strB := pullback.lift (abq 0).1 (abq 1).1 ((abq 0).2.trans (abq 1).2.symm)
    (NeronSpecialFibreInfra.fibreRestrictAlong (specMap (R p) κ) D₀.toBase D.toBase (δ 0)).1 = q ≫ Mx ≫ pullback.fst strB strB ∧
    (NeronSpecialFibreInfra.fibreRestrictAlong (specMap (R p) κ) D₀.toBase D.toBase (δ 1)).1 = q ≫ Mx ≫ pullback.snd strB strB := by sorry
