-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_fibrewiseAlgEquivZero_ofInvertible_norm_pullback_poincare
-- name    : ModularCurve.DRModelPackageLevel.fibrewiseAlgEquivZero_ofInvertible_norm_pullback_poincare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/9e81bd63-ddb7-562f-8160-c6a50c9944e3
-- title:
--   Norm of the pulled-back Poincaré bundle is fibrewise Pic⁰
-- statement:
--   Fix a nonzero $N_0$, a prime $p$ with $p \nmid N_0$, a Deligne–Rapoport model package $\mathfrak{P}$ of level $N_0,p$ (whose structure morphism is written `toBase N₀ p`), and a prime $\ell$. Let $\pi_1,\pi_2$ be morphisms from the level $N_0\ell,p$ model to the level $N_0,p$ model commuting with the two structure morphisms to $\operatorname{Spec}(R_p)$, with $\pi_2$ finite and surjective. Let $D$ be a relative $\operatorname{Pic}^0$ designation for `toBase N₀ p`, i.e. a scheme $D.P$ with a structure morphism $D.\mathrm{toBase}$ to $\operatorname{Spec}(R_p)$ and a zero section, and let $hD$ exhibit $D$ together with a Poincaré rigidified line bundle (rigidified along $\mathfrak{P}.\varepsilon_{\inf}$) as representing the subfunctor cut out by fibrewise algebraic equivalence to zero. Assume both base changes $X_{N_0\ell p}\times D.P$ and $X_{N_0p}\times D.P$ are integral, that the latter is normal in the sense that $\Gamma$ of each affine open is integrally closed, and that $D.\mathrm{toBase}$ is locally of finite type. Let $\mathrm{Nm}$ be an operation carrying a morphism $X \to Y$ and a module on $X$ to a module on $Y$, satisfying, for every finite surjective $\pi : X \to Y$ with $X,Y$ integral and $Y$ normal as above: preservation of invertibility; invariance under isomorphism of invertible modules; multiplicativity on tensor products of invertible modules; $\mathrm{Nm}\,\pi(\mathbf 1_X) \cong \mathbf 1_Y$; compatibility with flat base change along pullback squares (under the same integrality and normality assumptions on the base-changed schemes); and, over an open $V \subseteq Y$ on which $\pi$ restricts to a flat, locally finitely presented morphism of constant fibre rank $d$, agreement of $\mathrm{Nm}\,\pi(L)|_V$ with the determinant norm $\det{}_d(\pi_* L) \otimes \det{}_d(\pi_* \mathbf 1)^\vee$ of the restriction of $L$. Finally assume the module $M = \mathrm{Nm}_{\pi_2 \times D}\bigl((\pi_1\times D)^* \mathcal{P}\bigr)$ on $X_{N_0p}\times D.P$, formed with the base changes of $\pi_1,\pi_2$ along $D.\mathrm{toBase}$, is invertible. The conclusion is that the rigidified line bundle obtained from $M$ by rigidifying along $\mathfrak{P}.\varepsilon_{\inf}$ is fibrewise algebraically equivalent to zero: for every algebraically closed field $k$ and every $k$-point $s$ of $D.P$, the pullback of its underlying module to the fibre over $s$ is algebraically equivalent to zero.
--
--   This is the verification that the Hecke-type norm transform of the Poincaré bundle satisfies the $\operatorname{Pic}^0$ condition used to define the relative Picard functor represented by $D$, so that it is classified by a morphism of $D$ — the construction of the Hecke operator $T_\ell$ on the Jacobian of the Deligne–Rapoport model over $\mathbf{Z}_{(p)}$. It is used by [`ModularCurve.DRModelPackageLevel.exists_heckeHom_classifies_norm_pullback_poincare_of_flat`](thm.html#ModularCurve.DRModelPackageLevel.exists_heckeHom_classifies_norm_pullback_poincare_of_flat), which produces the classifying morphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_fibrewiseAlgEquivZero_ofInvertible_norm_pullback_poincare.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
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

theorem ModularCurve.DRModelPackageLevel.fibrewiseAlgEquivZero_ofInvertible_norm_pullback_poincare
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (ℓ : ℕ) [Fact ℓ.Prime]

    (π₁ π₂ : SchemeHomOver (toBase (N₀ * ℓ) p) (toBase N₀ p)) [IsFinite π₂.1] [Surjective π₂.1]

    (D : RelativePic0Designation (R p) (toBase N₀ p))
    (hD : RepresentsRelSubPic (toBase N₀ p) 𝔓.εinf (algEquivZeroCut (toBase N₀ p) 𝔓.εinf) D)

    [IsIntegral ↑(pullback (toBase (N₀ * ℓ) p) D.toBase)] [IsIntegral ↑(pullback (toBase N₀ p) D.toBase)]
    (hnorm : ∀ U : (pullback (toBase N₀ p) D.toBase).Opens, IsAffineOpen U →
      IsIntegrallyClosed Γ(pullback (toBase N₀ p) D.toBase, U))
    [LocallyOfFiniteType D.toBase]

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
              Scheme.Modules.normModule (π ∣_ V) d ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj L))))
    (hinv : Scheme.Modules.IsInvertible
      (Nm (curveChange π₂.1 π₂.2 D.toBase) ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L))) :
    FibrewiseAlgEquivZero (RigidifiedLineBundle.ofInvertible (ε := 𝔓.εinf)
      (Nm (curveChange π₂.1 π₂.2 D.toBase) ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L))
      hinv) := by sorry
