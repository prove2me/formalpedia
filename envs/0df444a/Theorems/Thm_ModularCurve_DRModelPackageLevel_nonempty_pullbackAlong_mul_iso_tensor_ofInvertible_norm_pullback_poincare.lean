-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_nonempty_pullbackAlong_mul_iso_tensor_ofInvertible_norm_pullback_poincare
-- name    : ModularCurve.DRModelPackageLevel.nonempty_pullbackAlong_mul_iso_tensor_ofInvertible_norm_pullback_poincare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/7bb90258-ec97-5f23-a482-4dc354d1d2a4
-- title:
--   Primitivity of the normed Poincaré bundle on T-points
-- statement:
--   Fix $N_0\neq 0$, a prime $p$ with $p\nmid N_0$, a package $\mathfrak{P}$ of type `DRModelPackageLevel N₀ p hpN₀` (which supplies among its fields the section $\varepsilon_\infty$ of `toBase N₀ p` over $\operatorname{Spec} R_p$), and a prime $\ell$. Let $\pi_1,\pi_2$ be morphisms over the base from the Igusa scheme of level $N_0\ell$ at $p$ to that of level $N_0$, i.e. morphisms $\varphi$ with $\varphi$ followed by `toBase N₀ p` equal to `toBase (N₀*ℓ) p`, with $\pi_2$ finite and surjective. Let $D$ consist of a scheme $P$, a morphism $D.\mathrm{toBase}\colon P\to\operatorname{Spec}R_p$ and a section of it, and let $hD$ witness that a rigidified line bundle `hD.poincare` on $X\times_{R_p}P$, fibrewise algebraically equivalent to zero, is universal for rigidified line bundles with that property (`RepresentsRelSubPic` for `algEquivZeroCut`). Assume $D.\mathrm{toBase}$ flat and locally of finite type, and assume integrality of the base changes of $X$ and $X'$ along $D.\mathrm{toBase}$ and along $\mathrm{pr}_1$ followed by $D.\mathrm{toBase}$ on $P\times_{R_p}P$, together with normality (integrally closed sections on affine opens) of the two base changes at level $N_0$; these integrality and normality hypotheses are summarised here. Let $Nm$ assign to every morphism of schemes a map from modules on the source to modules on the target, subject to $hNm$: for every finite surjective $\pi\colon X\to Y$ with $X,Y$ integral and $Y$ normal, $Nm\,\pi$ preserves invertibility, is invariant under isomorphism of invertible bundles, is multiplicative for tensor products of invertible bundles, carries the unit to the unit, commutes with flat base change along morphisms to integral normal schemes, and on an open $V\subseteq Y$ over which $\pi$ is flat, locally of finite presentation and of constant rank $d$ agrees with `Scheme.Modules.normModule`, that is with $\det_d$ of the pushforward tensored with the dual of $\det_d$ of the pushforward of the unit. Put $M = Nm$ of the curve-change morphism of $\pi_2$ over $D.\mathrm{toBase}$ applied to the pullback of `hD.poincare.L` along the curve-change morphism of $\pi_1$, and assume $M$ invertible ($hinv$). Let $M'$ be the rigidified line bundle `RigidifiedLineBundle.ofInvertible` attached to $M$ and $\varepsilon_\infty$, whose underlying module is $M$ tensored with the pullback along the second projection of the dual of the restriction of $M$ along the rigidifying section. Then for every scheme $T$, every $s\colon T\to\operatorname{Spec}R_p$ and all $T$-points $x,y$ of $D$ over $s$, the underlying module of the pullback of $M'$ along the product $x\cdot y$ for the group law on $T$-points of $D$ coming from representability (with the group condition `algEquivZeroGroupCut`) is isomorphic to the tensor product of the underlying modules of the pullbacks of $M'$ along $x$ and along $y$.
--
--   This is the statement that the $\pi_2$-norm of the $\pi_1$-pullback of the Poincaré bundle, rigidified at $\infty$, is a primitive (additive) line bundle on the model $D$ of the Jacobian of the modular curve of level $N_0$: its pullback along a sum of $T$-points is the tensor product of the pullbacks. It is the additivity input for [`ModularCurve.DRModelPackageLevel.exists_heckeHom_classifies_norm_pullback_poincare_of_flat`](thm.html#ModularCurve.DRModelPackageLevel.exists_heckeHom_classifies_norm_pullback_poincare_of_flat), which converts the Hecke correspondence $\pi_1,\pi_2$ into a morphism of group objects between the relative Picard models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_nonempty_pullbackAlong_mul_iso_tensor_ofInvertible_norm_pullback_poincare.lean

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

theorem ModularCurve.DRModelPackageLevel.nonempty_pullbackAlong_mul_iso_tensor_ofInvertible_norm_pullback_poincare
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
              Scheme.Modules.normModule (π ∣_ V) d ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj L))))
    (hinv : Scheme.Modules.IsInvertible
      (Nm (curveChange π₂.1 π₂.2 D.toBase) ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L)))
    {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (R p))) (x y : SchemeHomOver s D.toBase) :
    Nonempty (((RigidifiedLineBundle.ofInvertible (ε := 𝔓.εinf) (Nm (curveChange π₂.1 π₂.2 D.toBase) ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L)) hinv).pullbackAlong
        ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul s x y)).L ≅
      (((RigidifiedLineBundle.ofInvertible (ε := 𝔓.εinf) (Nm (curveChange π₂.1 π₂.2 D.toBase) ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L)) hinv).pullbackAlong x).tensor
        ((RigidifiedLineBundle.ofInvertible (ε := 𝔓.εinf) (Nm (curveChange π₂.1 π₂.2 D.toBase) ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L)) hinv).pullbackAlong y)).L) := by sorry
