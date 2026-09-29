-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_not_mem_kernelTrivial_away_of_kernelTrivial_atPrime_of_isNoetherianRing
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_not_mem_kernelTrivial_away_of_kernelTrivial_atPrime_of_isNoetherianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/f7fc1e36-000d-5b62-8b49-54c74575d077
-- title:
--   Triviality of K(τ) spreads from S_𝔭 to some S_g
-- statement:
--   Let $S$ be a noetherian commutative ring, $A$ a scheme and $f\colon A\to\operatorname{Spec}S$ a morphism equipped with a relative group law $L$, that is, a functorial group structure on the sets $\{\varphi\colon T\to A \mid \varphi\circ f = t\}$ of $S$-sections over arbitrary $t\colon T\to\operatorname{Spec}S$, compatible with precomposition in $T$. Assume `AbelianSchemePropertyBundle S f`: $f$ is smooth and proper, each set-theoretic fibre of $f$ is connected, and $f$ admits some relative group law. Let $\tau$ be a module on $A$ which is invertible, i.e. locally on $A$ isomorphic to the unit module, and let $\mathfrak p$ be a prime of $S$. Suppose given a relative group law $L_{\mathfrak p}$ on the base change $A\times_S\operatorname{Spec}S_{\mathfrak p}\to\operatorname{Spec}S_{\mathfrak p}$ which is compatible with $L$, in the sense that for all $T$, all $t'\colon T\to\operatorname{Spec}S_{\mathfrak p}$ and all sections $P,Q$ over $t'$, the first projection to $A$ of $L_{\mathfrak p}.\mathrm{mul}\,t'\,P\,Q$ equals the $L$-product of the projections of $P$ and $Q$, taken over $t'$ followed by $\operatorname{Spec}S_{\mathfrak p}\to\operatorname{Spec}S$. Assume `KernelTrivial` for this base change, $L_{\mathfrak p}$ and the pullback of $\tau$: for every commutative ring $R$, every $t\colon\operatorname{Spec}R\to\operatorname{Spec}S_{\mathfrak p}$ and every section $x$ over $t$, if the pullback along $\mathrm{sliceAt}\,x$ of the Mumford bundle $m^*\tau_{\mathfrak p}\otimes p_1^*\tau_{\mathfrak p}^\vee\otimes p_2^*\tau_{\mathfrak p}^\vee$ is `LocIsoOnBase` over the second projection to the unit module — i.e. every point of $\operatorname{Spec}R$ has an open neighbourhood over whose preimage the two become isomorphic — then $x$ is the unit section $L_{\mathfrak p}.\mathrm{one}\,t$. The conclusion: there exists $g\in S$ with $g\notin\mathfrak p$ such that for every relative group law $L_g$ on the base change $A\times_S\operatorname{Spec}S_g\to\operatorname{Spec}S_g$ satisfying the same compatibility with $L$, the corresponding `KernelTrivial` statement holds for $L_g$ and the pullback of $\tau$ to $A\times_S\operatorname{Spec}S_g$. Note the asymmetry: the hypothesis concerns one given group law over $S_{\mathfrak p}$, whereas the conclusion holds for all compatible group laws over $S_g$.
--
--   This is the spreading-out step for the condition $K(\tau)=e$, the triviality of the kernel of the polarisation attached to an invertible module on an abelian scheme: the condition, known over the local ring at a prime $\mathfrak p$, is propagated to a basic open neighbourhood $\operatorname{Spec}S_g$ of $\mathfrak p$. It feeds the passage from triviality over localisations at primes to triviality over localisations at powers, used in the construction of finite algebras carrying the relevant roots.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_not_mem_kernelTrivial_away_of_kernelTrivial_atPrime_of_isNoetherianRing.lean

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

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_not_mem_kernelTrivial_away_of_kernelTrivial_atPrime_of_isNoetherianRing
    {S : Type} [CommRing S] [IsNoetherianRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (τ : A.Modules) (hτ : Scheme.Modules.IsInvertible τ) (𝔭 : PrimeSpectrum S)
    (L𝔭 : RelativeGroupLaw (Localization.AtPrime 𝔭.asIdeal) (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal))))))
    (hL𝔭 : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of (Localization.AtPrime 𝔭.asIdeal)))
          (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))))),
          (L𝔭.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))) =
            (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal))))
              ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))),
                by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
              ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))),
                by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1))
    (hK : KernelTrivial (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal))))) L𝔭
      ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))))).obj τ)) :
    ∃ g : S, g ∉ 𝔭.asIdeal ∧
      ∀ (Lg : RelativeGroupLaw (Localization.Away g) (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g))))))
        (_ : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of (Localization.Away g)))
          (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))))),
          (Lg.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))) =
            (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g))))
              ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))),
                by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
              ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))),
                by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1)),
        KernelTrivial (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g))))) Lg
          ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))))).obj τ) := by sorry
