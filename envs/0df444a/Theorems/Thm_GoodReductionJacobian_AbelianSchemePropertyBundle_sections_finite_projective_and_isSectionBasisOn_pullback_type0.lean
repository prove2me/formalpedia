-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_sections_finite_projective_and_isSectionBasisOn_pullback_type0
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.sections_finite_projective_and_isSectionBasisOn_pullback_type0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/448d91f2-ff54-5add-881e-e21a266c6078
-- title:
--   Finite projective sections and base change of section bases
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} S$ a morphism carrying a relative group law $L$ (a functorial multiplication, unit and inverse on $S$-points of $f$ satisfying associativity, the unit laws, the left inverse law, and compatibility with base change) and satisfying `AbelianSchemePropertyBundle`, i.e. $f$ is smooth and proper, every fibre $f^{-1}(s)$ is connected, and $f$ admits a relative group law. Let $\mathcal L$ be a module on $A$ that is invertible (each point of $A$ has an open neighbourhood $U$ with the restriction of $\mathcal L$ to $U$ isomorphic to the unit sheaf of modules on $U$) and satisfies `ClosedImmersionBySections` for $f$: for some $N$ there is a projective presentation of $\mathcal L$ over $f$, consisting of sections $\sigma_0,\dots,\sigma_N \in \Gamma(\mathcal L,\top)$ and a morphism to $\operatorname{Proj}$ of the polynomial ring in $N+1$ variables over $S$ lying over $f$, frame-generating $\mathcal L$ on the preimages of the basic opens and matching the $\sigma_i$ by the coordinate ratios, whose structural morphism to $\operatorname{Proj}$ is a closed immersion. Four assertions follow, where $\Gamma(\mathcal L,\top)$ carries the $S$-module structure obtained from $f$ on global sections. First, $\Gamma(\mathcal L,\top)$ is a finite projective $S$-module. Second, for every point $s$ of $\operatorname{Spec} S$ there is $r \in S$ outside the prime of $s$ such that for every localisation $S'$ of $S$ away from $r$ and every cartesian square $g_A : A' \to A$, $f' : A' \to \operatorname{Spec} S'$ over $\operatorname{Spec}(S \to S')$, there are an $m$ and sections $\sigma' : \mathrm{Fin}\,m \to \Gamma(g_A^*\mathcal L, g_A^{-1}\top)$ forming a section basis on $g_A^{-1}\top$, meaning that $c \mapsto \sum_i f'^\sharp(c_i)\cdot\sigma'_i$ is a bijection from $\mathrm{Fin}\,m \to S'$. Third, if $\sigma : \mathrm{Fin}\,m \to \Gamma(\mathcal L,\top)$ is a section basis for $f$ in this sense, then for every ring homomorphism $\varphi : S \to S'$ and every cartesian square $g_A, f'$ over $\operatorname{Spec}\varphi$, the sections $g_A^*\sigma_i$ obtained from the unit of the pullback–pushforward adjunction form a section basis on $g_A^{-1}\top$ for $f'$. Fourth, for such a $\sigma$, every algebraically closed field $k$ and every homomorphism $sk : S \to k$, the $k$-dimension of the global sections of the pullback of $\mathcal L$ to $A \times_{\operatorname{Spec} S} \operatorname{Spec} k$ equals $m$.
--
--   This is the cohomology-and-base-change input for a relatively very ample invertible module on an abelian scheme, in the form needed later: global sections form a finite projective module, become free after a suitable localisation, their bases pull back along arbitrary base change, and the rank computes $h^0$ on every geometric fibre. It is used in the construction of moduli of framed polarised abelian schemes, in particular for the representability and quasi-projectivity statements and for level lifting over étale covers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_sections_finite_projective_and_isSectionBasisOn_pullback_type0.lean

import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.sections_finite_projective_and_isSectionBasisOn_pullback_type0
    {S : Type} [CommRing S] {A : Scheme} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (𝓛 : A.Modules) (hinv : Scheme.Modules.IsInvertible 𝓛) (hva : Scheme.Modules.ClosedImmersionBySections 𝓛 f) :
    (letI : Module S Γ(𝓛, ⊤) := Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appTop).hom
     Module.Finite S Γ(𝓛, ⊤) ∧ Module.Projective S Γ(𝓛, ⊤)) ∧
    (∀ s : ↥(Spec (CommRingCat.of S)), ∃ r : S, r ∉ s.asIdeal ∧
      ∀ (S' : Type) [CommRing S'] [Algebra S S'] [IsLocalization.Away r S']
        (A' : Scheme) (f' : A' ⟶ Spec (CommRingCat.of S')) (gA : A' ⟶ A),
        IsPullback gA f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))) →
        ∃ (m : ℕ) (σ' : Fin m → Γ((Scheme.Modules.pullback gA).obj 𝓛, gA ⁻¹ᵁ ⊤)),
          Scheme.Modules.IsSectionBasisOn f' ((Scheme.Modules.pullback gA).obj 𝓛) (gA ⁻¹ᵁ ⊤) σ') ∧
    (∀ {m : ℕ} (σ : Fin m → Γ(𝓛, ⊤)), Scheme.Modules.IsSectionBasis f 𝓛 σ →
      ∀ (S' : Type) [CommRing S'] (φ : S →+* S')
        (A' : Scheme) (f' : A' ⟶ Spec (CommRingCat.of S')) (gA : A' ⟶ A),
        IsPullback gA f' f (Spec.map (CommRingCat.ofHom φ)) →
        Scheme.Modules.IsSectionBasisOn f' ((Scheme.Modules.pullback gA).obj 𝓛) (gA ⁻¹ᵁ ⊤)
          (fun i => Scheme.Modules.pullbackLocalSection gA (σ i))) ∧
    (∀ {m : ℕ} (σ : Fin m → Γ(𝓛, ⊤)), Scheme.Modules.IsSectionBasis f 𝓛 σ →
      ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k), Scheme.Modules.geomFibreH0Finrank f 𝓛 k sk = m) := by sorry
