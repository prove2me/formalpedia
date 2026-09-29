-- Prove2me | Theorems.Thm_HopfAlgebra_exists_inertia_eigenvector_tameCharacter_pow_of_finite_flat_of_galoisSimple_of_exists_reductionKernel_map_ne_zero
-- name    : HopfAlgebra.exists_inertia_eigenvector_tameCharacter_pow_of_finite_flat_of_galoisSimple_of_exists_reductionKernel_map_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/42b9f18d-d4c4-50ed-ba52-f777ff4e03c2
-- title:
--   Inertia eigenvector from a reduction-kernel point with F≠ 0
-- statement:
--   Let $p$ be an odd prime and let $R$ denote the subring [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of the rationals whose denominator is coprime to $p$. Let $H$ be a commutative ring which is a cocommutative Hopf algebra over $R$, finite and flat as an $R$-module, and write $G_H$ for the monoid `WithConv` of $R$-algebra homomorphisms $H \to \overline{\mathbb{Q}}$ under convolution; assume every $f \in G_H$ satisfies $f^p = 1$. Let $P$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $P$, and let $I_P$ be the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of the decomposition subgroup of $P$. Let $N$ be a module over the residue field of $P$, let $\mathrm{act}$ assign to each $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ a linear endomorphism of $N$, and let $F : G_H \to N$ satisfy $F(fg) = F(f)+F(g)$, together with the equivariance: for $\sigma \in I_P$ and $f, g \in G_H$ with $g(h) = \sigma(f(h))$ for all $h \in H$, one has $F(g) = \mathrm{act}_\sigma(F(f))$. Assume further that $F$ is not identically zero; that every submonoid $S$ of $G_H$ stable under the Galois action (if $f \in S$ and $g(h)=\sigma(f(h))$ for all $h$, then $g \in S$) is $\bot$ or $\top$; and that some $f \in G_H$ lies in the reduction kernel, i.e. $P$-valuation of $f(h) - \varepsilon(h)$ (image under $R \to \overline{\mathbb{Q}}$ of the counit) is $<1$ for all $h \in H$, with $F(f) \neq 0$. Then there is an integer $s \geq 1$ such that for every $\pi' \in \overline{\mathbb{Q}}$ with $(\pi')^{p^s-1} = p$ there are a finite set $D$ of natural numbers, all $< s$, and a nonzero $w \in N$ with $\mathrm{act}_\sigma(w) = \theta_{\pi'}(\sigma)^{\sum_{j \in D} p^j} \cdot w$ for all $\sigma \in I_P$, where $\theta_{\pi'}(\sigma)$ is the residue of $\sigma(\pi')/\pi'$ when this lies in $P$ and $0$ otherwise.
--
--   This is the branch of Raynaud's eigenvector bound for finite flat group schemes of type $(p,\dots,p)$ over an absolutely unramified base in which $F$ is already nonzero on the reduction kernel at $P$; the conclusion exhibits an inertia eigenvector whose character is a power of the fundamental tame character with $p$-adic digits in $D$. It is one of the two cases combined in [`HopfAlgebra.exists_inertia_eigenvector_tameCharacter_pow_of_finite_flat_of_galoisSimple`](thm.html#HopfAlgebra.exists_inertia_eigenvector_tameCharacter_pow_of_finite_flat_of_galoisSimple).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_inertia_eigenvector_tameCharacter_pow_of_finite_flat_of_galoisSimple_of_exists_reductionKernel_map_ne_zero.lean

import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HopfAlgebra.exists_inertia_eigenvector_tameCharacter_pow_of_finite_flat_of_galoisSimple_of_exists_reductionKernel_map_ne_zero
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {H : Type} [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
    (hMp : ∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ), f ^ p = 1)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (N : Type) [AddCommGroup N] [Module (IsLocalRing.ResidueField P) N]
    (act : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → N →ₗ[IsLocalRing.ResidueField P] N)
    (F : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) → N)
    (hFmul : ∀ f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
      F (f * g) = F f + F g)
    (hFequiv : ∀ σ ∈ P.inertiaSubgroupIn ℚ,
      ∀ f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        (∀ h : H, g h = σ (f h)) → F g = act σ (F f))
    (hFne : ∃ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ), F f ≠ 0)
    (hSimple : ∀ S : Submonoid (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ f ∈ S,
        ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
          (∀ h : H, g h = σ (f h)) → g ∈ S) →
      S = ⊥ ∨ S = ⊤)
    (hFker : ∃ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
      (∀ h : H, P.valuation (f h -
        algebraMap (GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ) (Coalgebra.counit h)) < 1) ∧
      F f ≠ 0) :
    ∃ s : ℕ, 1 ≤ s ∧ ∀ π' : AlgebraicClosure ℚ, π' ^ (p ^ s - 1) = p →
      ∃ D : Finset ℕ, (∀ j ∈ D, j < s) ∧ ∃ w : N, w ≠ 0 ∧
        ∀ σ ∈ P.inertiaSubgroupIn ℚ,
          act σ w = P.tameCharacter π' σ ^ (∑ j ∈ D, p ^ j) • w := by sorry
