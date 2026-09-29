-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_heckeHom_classifies_norm_pullback_poincare_of_flat
-- name    : ModularCurve.DRModelPackageLevel.exists_heckeHom_classifies_norm_pullback_poincare_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/315fef36-9ac9-5342-9c97-5e8908770464
-- title:
--   Norm–pullback Hecke endomorphism of the Pic⁰ representing scheme
-- statement:
--   Fix $N_0 \neq 0$ and primes $p, \ell$ with $p \nmid N_0$, and let $\mathfrak{P}$ be a Deligne–Rapoport model package `DRModelPackageLevel N₀ p hpN₀`, whose structure morphism $\mathfrak{X} = X(N_0)_p \to \operatorname{Spec} R_p$ is written `toBase N₀ p`. Let $\pi_1, \pi_2$ be morphisms $X(N_0\ell)_p \to \mathfrak{X}$ commuting with the structure morphisms, with $\pi_2$ finite and surjective. Let $D$ consist of a scheme with a structure morphism $D \to \operatorname{Spec} R_p$ and a section `D.zeroSection`, and let $hD$ make $D$ represent the relative Picard condition cut out by fibrewise algebraic equivalence to zero, rigidified along $\mathfrak{P}.\varepsilon_{\infty}$: it supplies a rigidified invertible module `hD.poincare` on $\mathfrak{X} \times_{R_p} D$ satisfying that condition, universal for it, and trivial along the zero section. Assume $\mathfrak{X}' \times_{R_p} D$, $\mathfrak{X} \times_{R_p} D$, $\mathfrak{X}' \times_{R_p} (D \times_{R_p} D)$ and $\mathfrak{X} \times_{R_p} (D \times_{R_p} D)$ are integral (the products over $D\times D$ taken along the first projection followed by $D \to \operatorname{Spec} R_p$), that the two latter $\mathfrak{X}$-products have integrally closed sections on affine opens, and that $D \to \operatorname{Spec} R_p$ is flat and locally of finite type. Let $\mathrm{Nm}$ assign to each morphism of schemes a map on modules, subject to $h\mathrm{Nm}$: along any finite surjective $\pi : X \to Y$ of integral schemes with $Y$ having integrally closed affine sections, $\mathrm{Nm}\,\pi$ preserves invertibility, respects isomorphism of invertible modules, is multiplicative for tensor products of invertible modules, carries the unit to the unit, commutes with pullback along flat base change in a pullback square (under the corresponding integrality and normality hypotheses), and over an open $V \subseteq Y$ on which $\pi$ is flat, locally of finite presentation and of constant fibre rank $d$ agrees with `Scheme.Modules.normModule`, namely $\det_d(\pi_*L) \otimes \det_d(\pi_*\mathcal{O})^{\vee}$. Then there is an endomorphism $T_\ell$ of $D$ over $\operatorname{Spec} R_p$ such that the line bundle of `hD.poincare` pulled back along $T_\ell$ is isomorphic to the rigidification along `rigSection` of $\mathrm{Nm}$ taken along the base change of $\pi_2$ to $D$ of the pullback along the base change of $\pi_1$ to $D$ of that line bundle; $T_\ell$ is a homomorphism for the relative group law induced by $hD$, in the sense that composing the product of any two $T$-valued points with $T_\ell$ equals the product of their composites with $T_\ell$, for every $T \to \operatorname{Spec} R_p$; and $T_\ell$ fixes the zero section.
--
--   This realises the Hecke operator $T_\ell$ ($U_\ell$ when $\ell \mid N_0$) on the relative $\mathrm{Pic}^0$ of the Deligne–Rapoport model at level $N_0$ over $\mathbf{Z}_{(p)}$, as the correspondence $\mathrm{Nm}_{\pi_2} \circ \pi_1^{*}$ on the Poincaré bundle, together with the facts that the resulting endomorphism respects the group law and the origin. It feeds the construction of the Hecke action used to compare $\ell$-adic Tate modules of Jacobians, via `exists_hom_mul_and_pts_heckeOperatorBar_eq_comp_of_ne`; the present form strengthens an earlier version by also assuming integrality and normality of the products over $D \times_{R_p} D$, which is what the homomorphism property requires.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_exists_heckeHom_classifies_norm_pullback_poincare_of_flat.lean

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
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve ModularCurve.DRLevel

theorem ModularCurve.DRModelPackageLevel.exists_heckeHom_classifies_norm_pullback_poincare_of_flat
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (ℓ : ℕ) [Fact ℓ.Prime]

    (π₁ π₂ : SchemeHomOver (toBase (N₀ * ℓ) p) (toBase N₀ p)) [IsFinite π₂.1] [Surjective π₂.1]

    (D : RelativePic0Designation (R p) (toBase N₀ p))
    (hD : RepresentsRelSubPic (toBase N₀ p) 𝔓.εinf (algEquivZeroCut (toBase N₀ p) 𝔓.εinf) D)

    [IsIntegral ↑(pullback (toBase (N₀ * ℓ) p) D.toBase)] [IsIntegral ↑(pullback (toBase N₀ p) D.toBase)]
    (hnorm : ∀ U : (pullback (toBase N₀ p) D.toBase).Opens, IsAffineOpen U →
      IsIntegrallyClosed Γ(pullback (toBase N₀ p) D.toBase, U))

    [Flat D.toBase] [LocallyOfFiniteType D.toBase]
    [IsIntegral ↑(pullback (toBase (N₀ * ℓ) p) (pullback.fst D.toBase D.toBase ≫ D.toBase))]
    [IsIntegral ↑(pullback (toBase N₀ p) (pullback.fst D.toBase D.toBase ≫ D.toBase))]
    (hnorm₂ : ∀ U : (pullback (toBase N₀ p) (pullback.fst D.toBase D.toBase ≫ D.toBase)).Opens, IsAffineOpen U →
      IsIntegrallyClosed Γ(pullback (toBase N₀ p) (pullback.fst D.toBase D.toBase ≫ D.toBase), U))

    (Nm : ∀ ⦃X Y : Scheme.{0}⦄, (X ⟶ Y) → X.Modules → Y.Modules)
    (hNm :
      ∀ ⦃X Y : Scheme.{0}⦄ (π : X ⟶ Y) [IsFinite π] [Surjective π] [IsIntegral X] [IsIntegral Y],
        (∀ U : Y.Opens, IsAffineOpen U → IsIntegrallyClosed Γ(Y, U)) →

        (∀ L : X.Modules, Scheme.Modules.IsInvertible L → Scheme.Modules.IsInvertible (Nm π L)) ∧

        (∀ L L' : X.Modules, Scheme.Modules.IsInvertible L → Nonempty (L ≅ L') →
          Nonempty (Nm π L ≅ Nm π L')) ∧

        (∀ L L' : X.Modules, Scheme.Modules.IsInvertible L → Scheme.Modules.IsInvertible L' →
          Nonempty (Nm π (L ⊗ L') ≅ Nm π L ⊗ Nm π L')) ∧

        Nonempty (Nm π (𝟙_ X.Modules) ≅ 𝟙_ Y.Modules) ∧

        (∀ ⦃X' Y' : Scheme.{0}⦄ (g : Y' ⟶ Y) (π' : X' ⟶ Y') (g' : X' ⟶ X), IsPullback g' π' π g →
          ∀ [Flat g] [IsIntegral X'] [IsIntegral Y'],
          (∀ U : Y'.Opens, IsAffineOpen U → IsIntegrallyClosed Γ(Y', U)) →
          ∀ L : X.Modules, Scheme.Modules.IsInvertible L →
            Nonempty ((Scheme.Modules.pullback g).obj (Nm π L) ≅
              Nm π' ((Scheme.Modules.pullback g').obj L))) ∧

        (∀ (V : Y.Opens) (d : ℕ), Flat (π ∣_ V) → LocallyOfFinitePresentation (π ∣_ V) →
          (∀ y : V, (π ∣_ V).finrank y = d) →
          ∀ L : X.Modules, Scheme.Modules.IsInvertible L →
            Nonempty ((Scheme.Modules.pullback V.ι).obj (Nm π L) ≅
              Scheme.Modules.normModule (π ∣_ V) d ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj L)))) :
    ∃ Tℓ : SchemeHomOver D.toBase D.toBase,
      Nonempty ((hD.poincare.pullbackAlong Tℓ).L ≅
        Scheme.Modules.rigidify (rigSection (toBase N₀ p) D.toBase 𝔓.εinf) (pullback.snd (toBase N₀ p) D.toBase)
          (Nm (curveChange π₂.1 π₂.2 D.toBase)
            ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L))) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (x y : SchemeHomOver t D.toBase),
        NeronModelInfra.schemeHomOverComp
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul t x y) Tℓ =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul t
            (NeronModelInfra.schemeHomOverComp x Tℓ) (NeronModelInfra.schemeHomOverComp y Tℓ)) ∧
      D.zeroSection ≫ Tℓ.1 = D.zeroSection := by sorry
