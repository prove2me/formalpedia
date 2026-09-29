-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_finite_faithfullyFlat_atPrime_isSymmetric_locIsoOnBase_of_faithfullyFlat
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_finite_faithfullyFlat_atPrime_isSymmetric_locIsoOnBase_of_faithfullyFlat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/df2fbbb5-6b48-5704-9198-a9abc6e71386
-- title:
--   Symmetric square roots over a finite flat algebra over S_𝔭
-- statement:
--   Let $S$ be a noetherian commutative ring, $A$ a scheme and $f\colon A\to\operatorname{Spec}S$ a morphism equipped with a relative group law $L$ (a functorial group structure, natural in the base, on the sets of sections $T\to A$ over $\operatorname{Spec}S$), and assume the bundle of properties `AbelianSchemePropertyBundle` for $f$: $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and a relative group law exists. Let $\mathcal L$ be a module on $A$ which is invertible, i.e. every point has an open neighbourhood on which $\mathcal L$ restricts isomorphically to the unit sheaf of modules. Fix a prime $\mathfrak p$ of $S$, write $R_0=S_{\mathfrak p}$, and let $W$ be a commutative ring that is simultaneously an $S$- and an $R_0$-algebra compatibly, with $W$ faithfully flat over $R_0$. Suppose given an invertible module $\tau$ on $A_W=A\times_{\operatorname{Spec}S}\operatorname{Spec}W$ which is symmetric for the base-changed group law, that is, the pullback of $\tau$ along the inversion morphism $\mathrm{negMor}$ determined by $L.\mathrm{baseChange}$ and the identity section is, locally over the base $\operatorname{Spec}W$ (over some open neighbourhood of each point of the base, after pulling back to its preimage), isomorphic to $\tau$; and such that the pullback of $\mathcal L$ to $A_W$ is, in the same local-over-the-base sense, isomorphic to $\tau\otimes[-1]^*\tau$. The conclusion is the existence of a commutative ring $C_0$, an $S$-algebra and an $R_0$-algebra compatibly (as a scalar tower), such that $C_0$ is finite, faithfully flat and of finite presentation over $R_0$, together with an invertible module $M$ on $A_{C_0}$ which is symmetric for the group law base-changed to $C_0$ and satisfies, locally over $\operatorname{Spec}C_0$, an isomorphism between the pullback of $\mathcal L$ to $A_{C_0}$ and $M\otimes[-1]^*M$.
--
--   This is the descent step in the construction of symmetric square roots of a line bundle on an abelian scheme: a symmetric square root existing after a faithfully flat base change $W$ over the local ring $S_{\mathfrak p}$ is replaced by one over a finite, faithfully flat, finitely presented $S_{\mathfrak p}$-algebra, reflecting that the scheme of symmetric square roots is a torsor under the Cartier dual of $A[2]$ and hence finite flat over the base. It feeds the construction of principal symmetric square roots at a prime, used in the polarisation input to the good-reduction analysis of Jacobians.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_finite_faithfullyFlat_atPrime_isSymmetric_locIsoOnBase_of_faithfullyFlat.lean

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

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_finite_faithfullyFlat_atPrime_isSymmetric_locIsoOnBase_of_faithfullyFlat
    {S : Type} [CommRing S] [IsNoetherianRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (𝔭 : PrimeSpectrum S)
    (W : Type) [CommRing W] [Algebra S W] [Algebra (Localization.AtPrime 𝔭.asIdeal) W]
    [IsScalarTower S (Localization.AtPrime 𝔭.asIdeal) W] (hW : Module.FaithfullyFlat (Localization.AtPrime 𝔭.asIdeal) W)
    (τ : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S W)))).Modules) (hτ : Scheme.Modules.IsInvertible τ)
    (hroot : IsSymmetric (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S W)))) (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S W)))) τ ∧
        LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S W))))
          ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S W))))).obj 𝓛)
          (τ ⊗ (Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S W)))) (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S W)))))).obj τ)) :
    ∃ (C₀ : Type) (_ : CommRing C₀) (_ : Algebra S C₀) (_ : Algebra (Localization.AtPrime 𝔭.asIdeal) C₀)
      (_ : IsScalarTower S (Localization.AtPrime 𝔭.asIdeal) C₀),
      Module.Finite (Localization.AtPrime 𝔭.asIdeal) C₀ ∧ Module.FaithfullyFlat (Localization.AtPrime 𝔭.asIdeal) C₀ ∧
      Algebra.FinitePresentation (Localization.AtPrime 𝔭.asIdeal) C₀ ∧
      ∃ M : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S C₀)))).Modules, Scheme.Modules.IsInvertible M ∧
        IsSymmetric (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C₀)))) (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S C₀)))) M ∧
        LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))))
          ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))))).obj 𝓛)
          (M ⊗ (Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C₀)))) (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S C₀)))))).obj M) := by sorry
