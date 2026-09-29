-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_not_mem_finite_faithfullyFlat_symmetric_principalSqrt_of_faithfullyFlat_atPrime_of_isNoetherianRing
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_not_mem_finite_faithfullyFlat_symmetric_principalSqrt_of_faithfullyFlat_atPrime_of_isNoetherianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/20a1836d-aac2-5491-83ca-2f3ebf31d400
-- title:
--   Spreading symmetric principal square roots to a basic open
-- statement:
--   Let $S$ be a noetherian commutative ring, $A$ a scheme and $f\colon A\to\operatorname{Spec}S$ a morphism, equipped with a relative group law $L$ (a functorial group structure, compatible with base change, on the sets $\{\varphi\colon T\to A \mid \varphi\circ f^{-1}\text{-condition } \varphi \text{ followed by } f = t\}$ of sections over each $T\to\operatorname{Spec}S$), and assume the bundle of properties `AbelianSchemePropertyBundle`, i.e. $f$ is smooth and proper, every fibre $f^{-1}(s)$ is connected, and $f$ admits a relative group law. Let $\mathcal L$ be an $\mathcal O_A$-module that is invertible (every point of $A$ has a neighbourhood on which the restriction of $\mathcal L$ is isomorphic to the unit module), let $\mathfrak p$ be a prime of $S$, and let $W$ be a commutative ring that is an $S$-algebra and a $\operatorname{Localization.AtPrime}\mathfrak p$-algebra in a compatible tower, faithfully flat over $S_{\mathfrak p}$. Assume: for every relative group law $L'$ on the projection $\operatorname{pr}_2\colon A\times_{\operatorname{Spec}S}\operatorname{Spec}W\to\operatorname{Spec}W$ whose multiplication is compatible with $L$ along the first projection (the first component of $L'.\mathrm{mul}$ followed by $\operatorname{pr}_1$ equals the first component of the $L$-product of the two transported sections), there is an invertible module $\mathcal L_0$ on $A_W$ with `KernelTrivial` (for every affine base $\operatorname{Spec}R\to\operatorname{Spec}W$ and section $x$, local triviality over the base of the pullback along $x$'s slice of the Mumford bundle of $\mathcal L_0$ forces $x$ to be the identity section), `IsSymmetric` (the pullback of $\mathcal L_0$ along the inversion morphism of $L'$ is isomorphic to $\mathcal L_0$ after restriction over the preimages of a neighbourhood of each point of $\operatorname{Spec}W$), and, in the same local-on-the-base sense, $\operatorname{pr}_1^*\mathcal L\cong\mathcal L_0\otimes[-1]^*\mathcal L_0$. Then there exist $g\in S$ with $g\notin\mathfrak p$ and a commutative ring $C$, an $S$-algebra and a $\operatorname{Localization.Away}g$-algebra in a compatible tower, such that $C$ is finite, faithfully flat and of finite presentation over $\operatorname{Localization.Away}g$, and the identical root condition holds over $C$: every relative group law on $A_C\to\operatorname{Spec}C$ compatible with $L$ admits an invertible $\mathcal L_0$ on $A_C$ which is `KernelTrivial`, symmetric, and satisfies $\operatorname{pr}_1^*\mathcal L\cong\mathcal L_0\otimes[-1]^*\mathcal L_0$ locally over $\operatorname{Spec}C$.
--
--   This is the spreading-out step for symmetric principal square roots of a line bundle on an abelian scheme: a square root available over some faithfully flat algebra over the local ring at $\mathfrak p$ is replaced by one over a finite faithfully flat algebra of finite presentation over a basic open neighbourhood $\operatorname{Spec}S_g$ of $\mathfrak p$. It is used in the construction of canonical polarisation data on fake elliptic curves in the Čerednik–Drinfeld setting, where such data must be produced over an open cover of the base rather than at a single prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_not_mem_finite_faithfullyFlat_symmetric_principalSqrt_of_faithfullyFlat_atPrime_of_isNoetherianRing.lean

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

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_not_mem_finite_faithfullyFlat_symmetric_principalSqrt_of_faithfullyFlat_atPrime_of_isNoetherianRing
    {S : Type} [CommRing S] [IsNoetherianRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (𝔭 : PrimeSpectrum S)
    (W : Type) [CommRing W] [Algebra S W] [Algebra (Localization.AtPrime 𝔭.asIdeal) W]
    [IsScalarTower S (Localization.AtPrime 𝔭.asIdeal) W] (hW : Module.FaithfullyFlat (Localization.AtPrime 𝔭.asIdeal) W)
    (hroot : (∀ (L' : RelativeGroupLaw W (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S W))))),
          (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of W))
              (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S W))))),
              (L'.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S W))) =
                (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S W)))
                  ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S W))),
                    by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                  ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S W))),
                    by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
          ∃ 𝓛₀ : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S W)))).Modules,
            Scheme.Modules.IsInvertible 𝓛₀ ∧
            KernelTrivial (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S W)))) L' 𝓛₀ ∧
            IsSymmetric (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S W)))) L' 𝓛₀ ∧
            LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S W))))
              ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S W))))).obj 𝓛)
              (𝓛₀ ⊗ (Scheme.Modules.pullback
                (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S W)))) L')).obj 𝓛₀))) :
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
