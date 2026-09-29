-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_linearEquiv_tensorProduct_sections_pullback_type0
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_linearEquiv_tensorProduct_sections_pullback_type0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/b678a178-f4bb-5911-bf1e-ea3a961c189a
-- title:
--   Base change for global sections of an ample sheaf
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} S$ a morphism equipped with a relative group law $L$ (a functorial group structure on $S$-scheme sections of $f$), and assume the bundle of properties `AbelianSchemePropertyBundle` for $f$: $f$ is smooth, proper, each set-theoretic fibre of $f$ is connected, and a relative group law on $f$ exists. Let $\mathcal L$ be an $\mathcal O_A$-module which is invertible (every point of $A$ has an open neighbourhood $U$ on which the pullback of $\mathcal L$ along $U \hookrightarrow A$ is isomorphic to the unit sheaf) and which satisfies `ClosedImmersionBySections`: for some $N$ there is a `ProjPresentation` of $\mathcal L$ relative to $f$, i.e. global sections $\sigma_0,\dots,\sigma_N \in \Gamma(\mathcal L, \top)$ together with a morphism $A \to \mathbb P^N_S$ over $\operatorname{Spec} S$ trivialising $\mathcal L$ by $\sigma_i$ on the preimage of the $i$-th basic open and matching the coordinate ratios, whose map to $\mathbb P^N_S$ is a closed immersion. Let $\varphi : S \to S'$ be any ring homomorphism, $f' : A' \to \operatorname{Spec} S'$ a morphism and $g_A : A' \to A$ a morphism making the square $g_A, f', f, \operatorname{Spec}\varphi$ cartesian. Give $\Gamma(\mathcal L, \top)$ the $S$-module structure coming from $f$ on global sections, and $\Gamma(g_A^{*}\mathcal L, g_A^{-1}\top)$ the $S'$-module structure coming from $f'$, with $S'$ an $S$-algebra via $\varphi$. Then there is an $S'$-linear isomorphism $e : S' \otimes_S \Gamma(\mathcal L, \top) \to \Gamma(g_A^{*}\mathcal L, g_A^{-1}\top)$ with $e(s' \otimes \tau) = s' \cdot \mathrm{pullbackLocalSection}\,g_A\,\tau$ for all $s' \in S'$ and $\tau \in \Gamma(\mathcal L, \top)$, where `pullbackLocalSection` is the section obtained from $\tau$ by the unit of the pullback–pushforward adjunction.
--
--   This is cohomology and base change in degree $0$ for the sheaf defining a projective embedding of an abelian scheme: the formation of $\Gamma(A, \mathcal L)$ commutes with arbitrary base change $S \to S'$, the comparison map being induced by pullback of sections. It is the base-change input used in the construction of linear systems and section bases for polarised abelian schemes and in the associated moduli and level-structure statements, all stated at universe $0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_linearEquiv_tensorProduct_sections_pullback_type0.lean

import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_linearEquiv_tensorProduct_sections_pullback_type0
    {S : Type} [CommRing S] {A : Scheme} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (𝓛 : A.Modules) (hinv : Scheme.Modules.IsInvertible 𝓛) (hva : Scheme.Modules.ClosedImmersionBySections 𝓛 f)
    (S' : Type) [CommRing S'] (φ : S →+* S')
    (A' : Scheme) (f' : A' ⟶ Spec (CommRingCat.of S')) (gA : A' ⟶ A)
    (hg : IsPullback gA f' f (Spec.map (CommRingCat.ofHom φ))) :
    letI : Module S Γ(𝓛, ⊤) := Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appTop).hom
    letI : Module S' Γ((Scheme.Modules.pullback gA).obj 𝓛, gA ⁻¹ᵁ ⊤) :=
      Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of S')).inv ≫ f'.appLE ⊤ (gA ⁻¹ᵁ ⊤) le_top).hom
    letI : Algebra S S' := φ.toAlgebra
    ∃ e : S' ⊗[S] Γ(𝓛, ⊤) ≃ₗ[S'] Γ((Scheme.Modules.pullback gA).obj 𝓛, gA ⁻¹ᵁ ⊤),
      ∀ (s' : S') (τ : Γ(𝓛, ⊤)), e (s' ⊗ₜ[S] τ) = s' • Scheme.Modules.pullbackLocalSection gA τ := by sorry
