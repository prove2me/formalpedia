-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_nonempty_pullbackAlong_zeroSection_ofInvertible_norm_pullback_poincare_iso_unit
-- name    : ModularCurve.DRModelPackageLevel.nonempty_pullbackAlong_zeroSection_ofInvertible_norm_pullback_poincare_iso_unit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/fda0689b-828e-5e3a-b7c1-d5df548fc5c0
-- title:
--   Triviality along the zero section of the normed Poincaré bundle
-- statement:
--   Fix $N_0 \neq 0$ and a prime $p$ with $p \nmid N_0$, a package $\mathfrak{P}$ of type `DRModelPackageLevel N₀ p hpN₀` (so in particular the structure morphism $c =$ `toBase N₀ p` from $X =$ `X N₀ p` to $\operatorname{Spec} R_p$ is proper, flat, locally of finite presentation with $X$ integral and all affine sections integrally closed, and $\mathfrak{P}$ provides the section $\varepsilon_{\infty}$), and a prime $\ell$. Let $\pi_1, \pi_2$ be morphisms $X(N_0\ell) \to X(N_0)$ over $\operatorname{Spec} R_p$, i.e. morphisms composing with `toBase N₀ p` to `toBase (N₀ * ℓ) p`, with $\pi_2$ finite and surjective. Let $D$ consist of a scheme $P$ with a morphism `D.toBase` to $\operatorname{Spec} R_p$ and a zero section, and let `hD` witness that $D$ represents the condition `algEquivZeroCut c 𝔓.εinf`, i.e. it carries a Poincaré rigidified line bundle `hD.poincare` on $X \times_{R_p} P$, fibrewise algebraically equivalent to zero, universal among such rigidified bundles, and trivial along the zero section. Assume $X(N_0\ell) \times_{R_p} P$ and $X \times_{R_p} P$ are integral, all affine sections of $X \times_{R_p} P$ are integrally closed, and `D.toBase` is locally of finite type. Let $\mathrm{Nm}$ assign to each morphism of schemes a map on modules, satisfying, for every finite surjective $\pi : X' \to Y'$ of integral schemes with $Y'$ having integrally closed affine sections: preservation of invertibility, invariance under isomorphism of an invertible source, multiplicativity on tensor products of invertibles, triviality on the unit, compatibility with flat base change along pullback squares of integral schemes with the same normality hypothesis, and agreement with `Scheme.Modules.normModule` of rank $d$ over any open on which $\pi$ restricts to a flat, locally finitely presented morphism of constant rank $d$. Write $M = \mathrm{Nm}_{\pi_2 \times P}\bigl((\pi_1 \times P)^{*} \,\mathrm{hD.poincare.L}\bigr)$, where $\pi_i \times P$ denotes `curveChange` of $\pi_i$ along `D.toBase`, and assume $M$ invertible. Let finally $V$ be an open of $X$, $d$ a natural number, such that $\pi_2$ restricted over $V$ is flat and locally of finite presentation with rank $d$ at every point of $V$, and such that $V$ contains every $x \in X$ whose local ring has Krull dimension at most $1$. The conclusion is twofold: the pullback of $M$ along the base change of the zero section, a morphism $X \times_{R_p} \operatorname{Spec} R_p \to X \times_{R_p} P$, is isomorphic to the unit module of $X \times_{R_p} \operatorname{Spec} R_p$; and the rigidified line bundle `RigidifiedLineBundle.ofInvertible` attached to $M$ with respect to $\varepsilon_{\infty}$, pulled back along the zero section, has underlying module isomorphic to that of the unit rigidified line bundle over the identity of $\operatorname{Spec} R_p$ — exactly the shape of the zero-section clause of a representing datum.
--
--   This is the zero-section normalisation required to regard the norm, along a degeneracy map, of the pulled-back Poincaré bundle as a rigidified line bundle of the same kind as those classified by the relative $\operatorname{Pic}^0$ datum of the Deligne–Rapoport model; the second clause matches the `zero` field of `RepresentsRelSubPic`. It is used in the construction of the induced Hecke-type morphism on the relative Picard scheme and in the verification that the normed bundle is fibrewise algebraically equivalent to zero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_nonempty_pullbackAlong_zeroSection_ofInvertible_norm_pullback_poincare_iso_unit.lean

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

theorem ModularCurve.DRModelPackageLevel.nonempty_pullbackAlong_zeroSection_ofInvertible_norm_pullback_poincare_iso_unit
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
      (Nm (curveChange π₂.1 π₂.2 D.toBase) ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L)))

    (V : (X N₀ p).Opens) (d : ℕ) [Flat (π₂.1 ∣_ V)] [LocallyOfFinitePresentation (π₂.1 ∣_ V)]
    (hrk : ∀ y : V, (π₂.1 ∣_ V).finrank y = d)
    (hVcodim : ∀ x : X N₀ p, ringKrullDim ((X N₀ p).presheaf.stalk x) ≤ 1 → x ∈ V) :

    Nonempty ((Scheme.Modules.pullback (baseChangeSnd (toBase N₀ p)
        (⟨D.zeroSection, D.zeroSection_toBase⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R p)))) D.toBase))).obj
      (Nm (curveChange π₂.1 π₂.2 D.toBase) ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L)) ≅
      SheafOfModules.unit (pullback (toBase N₀ p) (𝟙 (Spec (CommRingCat.of (R p))))).ringCatSheaf) ∧

    Nonempty (((RigidifiedLineBundle.ofInvertible (ε := 𝔓.εinf)
        (Nm (curveChange π₂.1 π₂.2 D.toBase) ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L)) hinv).pullbackAlong
        ⟨D.zeroSection, D.zeroSection_toBase⟩).L ≅
      (RigidifiedLineBundle.unit (c := toBase N₀ p) (ε := 𝔓.εinf) (𝟙 _)).L) := by sorry
