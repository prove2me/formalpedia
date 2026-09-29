-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_kernelTrivial_of_isSymmetric_of_locIsoOnBase_of_finite_atPrime_of_faithfullyFlat
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.kernelTrivial_of_isSymmetric_of_locIsoOnBase_of_finite_atPrime_of_faithfullyFlat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/f87f5d32-e151-5985-a5c3-e62748a1d199
-- title:
--   Kernel triviality for a symmetric square root over a finite algebra
-- statement:
--   Let $S$ be a noetherian commutative ring, $A$ a scheme and $f\colon A\to\operatorname{Spec} S$ a morphism carrying a relative group law $L$ (functorial multiplication, unit and inversion on sections over varying $S$-schemes), and assume the bundle `AbelianSchemePropertyBundle` for $f$: $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and $f$ admits a relative group law. Let $\mathcal L$ be a module on $A$ that is invertible (locally on $A$ its restriction is isomorphic to the unit sheaf), and let $\mathfrak p$ be a prime of $S$. Let $W$ be an $S$-algebra and an $S_{\mathfrak p}$-algebra compatibly, faithfully flat over $S_{\mathfrak p}$, and let $\tau$ be an invertible module on $A_W=A\times_{\operatorname{Spec} S}\operatorname{Spec} W$ such that (i) $\tau$ has trivial kernel for the base-changed group law, i.e. for every commutative ring $R$, every $t\colon\operatorname{Spec} R\to\operatorname{Spec} W$ and every section $x$ of $A_W$ over $t$, if the pullback along the slice of $x$ of the Mumford bundle $m^*\tau\otimes p_1^*\tau^{\vee}\otimes p_2^*\tau^{\vee}$ is, locally on $\operatorname{Spec} R$, isomorphic to the unit, then $x$ is the unit section; and (ii) locally on $\operatorname{Spec} W$ the pullback of $\mathcal L$ to $A_W$ is isomorphic to $\tau\otimes[-1]^*\tau$, where $[-1]$ is the inversion morphism of the base-changed law. Let $C_0$ be an $S$-algebra and $S_{\mathfrak p}$-algebra compatibly, finite as an $S_{\mathfrak p}$-module, and let $M$ be an invertible module on $A_{C_0}$ with $[-1]^*M$ and $M$ isomorphic locally on $\operatorname{Spec} C_0$, and with the pullback of $\mathcal L$ isomorphic to $M\otimes[-1]^*M$ locally on $\operatorname{Spec} C_0$. Then $M$ has trivial kernel over $C_0$: in the sense of (i) above for $A_{C_0}$ and the base-changed group law, any section whose slice of the Mumford bundle of $M$ is locally trivial is the unit section.
--
--   In classical terms: a symmetric square root $M$ of $\mathcal L$ over a finite algebra over the local ring $S_{\mathfrak p}$ has trivial Mumford kernel $K(M)=e$, deduced from the existence of a square root with trivial kernel over some faithfully flat extension $W$ of $S_{\mathfrak p}$ via the fact that then $K(\mathcal L)$ is the $2$-torsion on geometric fibres. It feeds the construction of symmetric principal square roots used in the polarisation and Rosati formalism for the Jacobian of good reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_kernelTrivial_of_isSymmetric_of_locIsoOnBase_of_finite_atPrime_of_faithfullyFlat.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.kernelTrivial_of_isSymmetric_of_locIsoOnBase_of_finite_atPrime_of_faithfullyFlat
    {S : Type} [CommRing S] [IsNoetherianRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (𝔭 : PrimeSpectrum S)
    (W : Type) [CommRing W] [Algebra S W] [Algebra (Localization.AtPrime 𝔭.asIdeal) W]
    [IsScalarTower S (Localization.AtPrime 𝔭.asIdeal) W] (hW : Module.FaithfullyFlat (Localization.AtPrime 𝔭.asIdeal) W)
    (τ : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S W)))).Modules) (hτ : Scheme.Modules.IsInvertible τ)
    (hKτ : KernelTrivial (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S W)))) (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S W)))) τ)
    (hrτ : LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S W))))
      ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S W))))).obj 𝓛)
      (τ ⊗ (Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S W)))) (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S W)))))).obj τ))
    (C₀ : Type) [CommRing C₀] [Algebra S C₀] [Algebra (Localization.AtPrime 𝔭.asIdeal) C₀]
    [IsScalarTower S (Localization.AtPrime 𝔭.asIdeal) C₀] [Module.Finite (Localization.AtPrime 𝔭.asIdeal) C₀]
    (M : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S C₀)))).Modules) (hM : Scheme.Modules.IsInvertible M)
    (hsM : IsSymmetric (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C₀)))) (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S C₀)))) M ∧
        LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))))
          ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))))).obj 𝓛)
          (M ⊗ (Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C₀)))) (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S C₀)))))).obj M)) :
    KernelTrivial (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C₀)))) (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S C₀)))) M := by sorry
