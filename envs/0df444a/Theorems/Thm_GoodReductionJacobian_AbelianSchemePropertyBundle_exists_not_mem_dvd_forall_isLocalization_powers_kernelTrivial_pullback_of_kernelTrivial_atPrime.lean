-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_not_mem_dvd_forall_isLocalization_powers_kernelTrivial_pullback_of_kernelTrivial_atPrime
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_not_mem_dvd_forall_isLocalization_powers_kernelTrivial_pullback_of_kernelTrivial_atPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/b1e6271e-e9c9-5cd5-a605-eecd7a26989e
-- title:
--   Spreading out kernel triviality from the local stage to a neighbourhood
-- statement:
--   Let $S$ be a noetherian commutative ring, $f\colon A\to\operatorname{Spec}S$ a morphism of schemes, $L$ a relative group law on $f$ (a functorial group structure on sections of $f$ over varying $S$-schemes), and assume the bundle of properties `AbelianSchemePropertyBundle` for $f$: $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and $f$ admits some relative group law. Let $\mathfrak p$ be a prime of $S$ and $g_1\notin\mathfrak p$; let $C$ be an $S$-algebra which is also a $S[1/g_1]$-algebra compatibly and is module-finite over $S[1/g_1]$. Let $C_0$ be a $C$-algebra, compatibly an $S$-algebra, which is the localisation of $C$ at the image of $S\setminus\mathfrak p$, and let $L_0$ be a relative group law on the base change $A_{C_0}\to\operatorname{Spec}C_0$ (the second projection of the pullback of $f$ along $\operatorname{Spec}C_0\to\operatorname{Spec}S$) which is compatible with $L$: for all $T$, all $t'\colon T\to\operatorname{Spec}C_0$ and all sections $P,Q$ over $t'$, the first projection of $L_0.\mathrm{mul}\,t'\,P\,Q$ is $L.\mathrm{mul}$ applied to the projections of $P$ and $Q$. Let $r_1\in S$ with $r_1\notin\mathfrak p$, let $C_1$ be a $C$-algebra, compatibly an $S$-algebra, which is the localisation of $C$ at the image of the powers of $r_1$, let $\varphi_0\colon C_1\to C_0$ be a ring homomorphism over $C$, and let $\rho_0\colon A_{C_0}\to A_{C_1}$ satisfy the two compatibilities: composing with the first projection gives the first projection of $A_{C_0}$, and composing with the second projection gives the second projection of $A_{C_0}$ followed by $\operatorname{Spec}\varphi_0$. Let $\mathcal L_1$ be an invertible module on $A_{C_1}$ (locally on $A_{C_1}$ isomorphic to the unit), and assume `KernelTrivial` for $A_{C_0}\to\operatorname{Spec}C_0$, $L_0$ and $\rho_0^*\mathcal L_1$, that is: for every commutative ring $R$, every $t\colon\operatorname{Spec}R\to\operatorname{Spec}C_0$ and every section $x$ of $A_{C_0}$ over $t$, if the pullback along the slice morphism at $x$ of the Mumford bundle $\mathrm{m}^*\mathcal M\otimes p_1^*\mathcal M^\vee\otimes p_2^*\mathcal M^\vee$ of $\mathcal M=\rho_0^*\mathcal L_1$ is, locally on $\operatorname{Spec}R$, isomorphic to the unit module, then $x$ is the identity section. The conclusion asserts the existence of $r\in S$ with $r\notin\mathfrak p$ and $r_1\mid r$ such that for every $C$-algebra $C'$, compatibly an $S$-algebra, realising the localisation of $C$ at the image of the powers of $r$, every ring homomorphism $\varphi\colon C_1\to C'$ over $C$, every $\rho\colon A_{C'}\to A_{C_1}$ satisfying the same two projection compatibilities with respect to $\varphi$, and every relative group law $L'$ on $A_{C'}$ compatible with $L$ in the above sense, `KernelTrivial` holds for $A_{C'}\to\operatorname{Spec}C'$, $L'$ and $\rho^*\mathcal L_1$.
--
--   This is the spreading-out step for the condition $K(\mathcal L)=e$ on an abelian scheme: triviality of the kernel of a line bundle, known over the localisation of $C$ at $\mathfrak p$, is propagated to all further localisations $C[1/r]$ for a single $r\notin\mathfrak p$ divisible by the previously chosen $r_1$, so that the stage data $(\varphi,\rho,L')$ may be refined freely afterwards. It is obtained from the corresponding statement for $C$ finite over a localisation of $S$, and is used in the construction of symmetric principal square roots over a localisation at the powers of a single element.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_not_mem_dvd_forall_isLocalization_powers_kernelTrivial_pullback_of_kernelTrivial_atPrime.lean

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

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_not_mem_dvd_forall_isLocalization_powers_kernelTrivial_pullback_of_kernelTrivial_atPrime
    {S : Type} [CommRing S] [IsNoetherianRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f) (𝔭 : PrimeSpectrum S)
    (g₁ : S) (hg₁ : g₁ ∉ 𝔭.asIdeal)
    (C : Type) [CommRing C] [Algebra S C] [Algebra (Localization.Away g₁) C] [IsScalarTower S (Localization.Away g₁) C]
    (hCfin : Module.Finite (Localization.Away g₁) C)
    (C₀ : Type) [CommRing C₀] [Algebra S C₀] [Algebra C C₀] [IsScalarTower S C C₀]
    [IsLocalization (Algebra.algebraMapSubmonoid C 𝔭.asIdeal.primeCompl) C₀]
    (L₀ : RelativeGroupLaw C₀ (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C₀)))))
    (hL₀ : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of C₀))
        (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))))),
        (L₀.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))) =
          (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S C₀)))
            ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))),
              by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))),
              by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1))
    (r₁ : S) (hr₁ : r₁ ∉ 𝔭.asIdeal)
    (C₁ : Type) [CommRing C₁] [Algebra S C₁] [Algebra C C₁] [IsScalarTower S C C₁]
    [IsLocalization (Algebra.algebraMapSubmonoid C (Submonoid.powers r₁)) C₁]
    (φ₀ : C₁ →+* C₀) (hφ₀ : φ₀.comp (algebraMap C C₁) = algebraMap C C₀)
    (ρ₀ : pullback f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap S C₁))))
    (hρ₀₁ : ρ₀ ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C₁))) = pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))))
    (hρ₀₂ : ρ₀ ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C₁))) = pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))) ≫ Spec.map (CommRingCat.ofHom φ₀))
    (𝓛₁ : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S C₁)))).Modules) (h𝓛₁ : Scheme.Modules.IsInvertible 𝓛₁)
    (hKT₀ : KernelTrivial (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C₀)))) L₀ ((Scheme.Modules.pullback ρ₀).obj 𝓛₁)) :
    ∃ r : S, r ∉ 𝔭.asIdeal ∧ r₁ ∣ r ∧
      ∀ (C' : Type) [CommRing C'] [Algebra S C'] [Algebra C C'] [IsScalarTower S C C']
    [IsLocalization (Algebra.algebraMapSubmonoid C (Submonoid.powers r)) C']
        (φ : C₁ →+* C') (_ : φ.comp (algebraMap C C₁) = algebraMap C C')
        (ρ : pullback f (Spec.map (CommRingCat.ofHom (algebraMap S C'))) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap S C₁))))
    (_ : ρ ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C₁))) = pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C'))))
    (_ : ρ ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C₁))) = pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C'))) ≫ Spec.map (CommRingCat.ofHom φ))
        (L' : RelativeGroupLaw C' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C')))))
        (_ : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of C'))
        (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C'))))),
        (L'.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C'))) =
          (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S C')))
            ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C'))),
              by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C'))),
              by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1)),
        KernelTrivial (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C')))) L' ((Scheme.Modules.pullback ρ).obj 𝓛₁) := by sorry
