-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_isOpen_forall_isSectionBasisOn_pullback_iff
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_isOpen_forall_isSectionBasisOn_pullback_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/2fd2f79b-dca9-519d-8ad2-3c6af6397075
-- title:
--   Open locus where pulled-back sections form a basis
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} S$ a morphism, equipped with a relative group law $L$ for $f$ (a functorial group structure on the sets of $T$-valued points of $A$ over $\operatorname{Spec} S$, compatible with base change along maps $T' \to T$) and with the property bundle `AbelianSchemePropertyBundle`, i.e. $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and $f$ admits a relative group law. Let $\mathcal{L}$ be a module sheaf on $A$ which is invertible (every point has a neighbourhood $U$ with $\mathcal{L}|_U$ isomorphic to the unit sheaf) and which satisfies `ClosedImmersionBySections` relative to $f$: for some $N$ there is a projective presentation of $\mathcal{L}$ over $f$ — global sections $\sigma_0,\dots,\sigma_N$ of $\mathcal{L}$ together with a morphism $A \to \mathbf{P}^N_S$ over $\operatorname{Spec} S$ trivialising $\mathcal{L}$ on the preimages of the standard basic opens and matching the $\sigma_i$ with the coordinate ratios — whose structural morphism to $\mathbf{P}^N_S$ is a closed immersion. Let $\tau_0,\dots,\tau_{m-1} \in \Gamma(\mathcal{L}, \top)$. Then there is an open set $U \subseteq \operatorname{Spec} S$ with the following property: for every commutative ring $S'$, every ring homomorphism $\varphi : S \to S'$, and every scheme $A'$ with morphisms $f' : A' \to \operatorname{Spec} S'$ and $g_A : A' \to A$ forming a cartesian square over $\operatorname{Spec} \varphi$, the pulled-back sections $g_A^{*}\tau_i$ of $g_A^{*}\mathcal{L}$ on $g_A^{-1}(\top)$ are a section basis for $f'$ — that is, the map $(c_i) \mapsto \sum_i \varphi\text{-scalar}(c_i) \cdot g_A^{*}\tau_i$ from $S'^{\,m}$ to $\Gamma(g_A^{*}\mathcal{L}, g_A^{-1}(\top))$, the scalars acting through $f'^{\#}$, is bijective — if and only if the image of $\operatorname{Spec} S' \to \operatorname{Spec} S$ is contained in $U$.
--
--   This is the statement that the locus where $m$ given sections of a relatively very ample invertible sheaf on an abelian scheme become an $S'$-basis of the sections after base change is an open subfunctor of $\operatorname{Spec} S$, in the form of a single open subset of $\operatorname{Spec} S$ detecting the condition through the image of $\operatorname{Spec} S' \to \operatorname{Spec} S$. It is used in the construction of the framed polarised abelian scheme moduli problem, in particular for the representability and quasi-projectivity statements and for the base-change statement for framed polarised abelian schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_isOpen_forall_isSectionBasisOn_pullback_iff.lean

import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_isOpen_forall_isSectionBasisOn_pullback_iff
    {S : Type} [CommRing S] {A : Scheme} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (𝓛 : A.Modules) (hinv : Scheme.Modules.IsInvertible 𝓛) (hva : Scheme.Modules.ClosedImmersionBySections 𝓛 f)
    {m : ℕ} (τ : Fin m → Γ(𝓛, ⊤)) :
    ∃ U : Set ↥(Spec (CommRingCat.of S)), IsOpen U ∧
      ∀ (S' : Type) [CommRing S'] (φ : S →+* S')
        (A' : Scheme) (f' : A' ⟶ Spec (CommRingCat.of S')) (gA : A' ⟶ A),
        IsPullback gA f' f (Spec.map (CommRingCat.ofHom φ)) →
        (Scheme.Modules.IsSectionBasisOn f' ((Scheme.Modules.pullback gA).obj 𝓛) (gA ⁻¹ᵁ ⊤)
            (fun i => Scheme.Modules.pullbackLocalSection gA (τ i)) ↔
          Set.range (PrimeSpectrum.comap φ) ⊆ U) := by sorry
