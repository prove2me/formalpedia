-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_not_mem_finite_faithfullyFlat_symmetric_principalSqrt_of_finite_atPrime
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_not_mem_finite_faithfullyFlat_symmetric_principalSqrt_of_finite_atPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/5ab69ad7-b61d-57b9-b03a-d43bbfaac2a8
-- title:
--   Spreading a symmetric principal square root to a basic open neighbourhood
-- statement:
--   Let $S$ be a noetherian commutative ring, $A$ a scheme with a morphism $f\colon A\to\operatorname{Spec} S$, $L$ a relative group law on $f$ (functorial group structure on sections over arbitrary $S$-schemes), and let `AbelianSchemePropertyBundle` hold for $f$: $f$ is smooth and proper, each fibre of $f$ is connected, and $f$ carries some relative group law. Let $\mathcal L$ be a module on $A$ that is invertible (locally on $A$ isomorphic to the unit), and $\mathfrak p$ a prime of $S$. Let $C_0$ be a commutative ring which is an $S$-algebra and an $S_{\mathfrak p}=$`Localization.AtPrime 𝔭.asIdeal`-algebra compatibly, and assume $C_0$ is finite, faithfully flat and of finite presentation over $S_{\mathfrak p}$ and satisfies the root property: for every relative group law $L'$ on the base change $A_{C_0}\to\operatorname{Spec} C_0$ whose multiplication is carried by the first projection to that of $L$, there is an invertible module $\mathcal L_0$ on $A_{C_0}$ which is `KernelTrivial` for $L'$ (a section $x$ over $\operatorname{Spec} R$ equals the identity section whenever the slice of the Mumford bundle of $\mathcal L_0$ at $x$ is, locally on the base, isomorphic to the unit), is symmetric (the pullback along the $L'$-inversion morphism is, locally on the base, isomorphic to $\mathcal L_0$), and satisfies $\mathcal L_0\otimes[-1]^{*}\mathcal L_0\cong$ the pullback of $\mathcal L$ locally on the base. Then there exist $g\in S\setminus\mathfrak p$ and a commutative ring $C$, an $S$-algebra and compatibly a `Localization.Away g`-algebra, finite, faithfully flat and of finite presentation over `Localization.Away g`, satisfying the same root property with $C$ in place of $C_0$.
--
--   This is the spreading-out step for symmetric principal square roots of a line bundle on an abelian scheme: a finite flat cover of the local ring $S_{\mathfrak p}$ over which $\mathcal L$ acquires a symmetric principal square root is replaced by a finite flat cover of a basic open neighbourhood $\operatorname{Spec} S_g$ of $\mathfrak p$. It feeds the construction of a noetherian global root cover, used in the Rosati/polarisation part of the abelian-scheme infrastructure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_not_mem_finite_faithfullyFlat_symmetric_principalSqrt_of_finite_atPrime.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_not_mem_finite_faithfullyFlat_symmetric_principalSqrt_of_finite_atPrime
    {S : Type} [CommRing S] [IsNoetherianRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (𝔭 : PrimeSpectrum S)
    (C₀ : Type) [CommRing C₀] [Algebra S C₀] [Algebra (Localization.AtPrime 𝔭.asIdeal) C₀] [IsScalarTower S (Localization.AtPrime 𝔭.asIdeal) C₀]
    (hC₀ : Module.Finite (Localization.AtPrime 𝔭.asIdeal) C₀ ∧ Module.FaithfullyFlat (Localization.AtPrime 𝔭.asIdeal) C₀ ∧
      Algebra.FinitePresentation (Localization.AtPrime 𝔭.asIdeal) C₀ ∧
      (∀ (L' : RelativeGroupLaw C₀ (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))))),
          (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of C₀))
              (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))))),
              (L'.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))) =
                (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S C₀)))
                  ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))),
                    by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                  ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))),
                    by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
          ∃ 𝓛₀ : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S C₀)))).Modules,
            Scheme.Modules.IsInvertible 𝓛₀ ∧
            KernelTrivial (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C₀)))) L' 𝓛₀ ∧
            IsSymmetric (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C₀)))) L' 𝓛₀ ∧
            LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))))
              ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))))).obj 𝓛)
              (𝓛₀ ⊗ (Scheme.Modules.pullback
                (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C₀)))) L')).obj 𝓛₀))) :
    ∃ (g : S) (_ : g ∉ 𝔭.asIdeal) (C : Type) (_ : CommRing C) (_ : Algebra S C) (_ : Algebra (Localization.Away g) C)
      (_ : IsScalarTower S (Localization.Away g) C),
      Module.Finite (Localization.Away g) C ∧ Module.FaithfullyFlat (Localization.Away g) C ∧
      Algebra.FinitePresentation (Localization.Away g) C ∧
      (∀ (L' : RelativeGroupLaw C (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C))))),
          (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of C))
              (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C))))),
              (L'.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C))) =
                (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S C)))
                  ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C))),
                    by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                  ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C))),
                    by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
          ∃ 𝓛₀ : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S C)))).Modules,
            Scheme.Modules.IsInvertible 𝓛₀ ∧
            KernelTrivial (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C)))) L' 𝓛₀ ∧
            IsSymmetric (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C)))) L' 𝓛₀ ∧
            LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C))))
              ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C))))).obj 𝓛)
              (𝓛₀ ⊗ (Scheme.Modules.pullback
                (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C)))) L')).obj 𝓛₀)) := by sorry
