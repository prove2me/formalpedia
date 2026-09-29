-- Prove2me | Theorems.Thm_HopfAlgebra_exists_inertia_eigenvector_tameCharacter_pow_of_finite_flat_of_galoisSimple
-- name    : HopfAlgebra.exists_inertia_eigenvector_tameCharacter_pow_of_finite_flat_of_galoisSimple
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/762838af-5d26-587a-ac79-2851ee3942b6
-- title:
--   Raynaud digit bound, Galois-simple case: inertia eigenvector for a tame character power
-- statement:
--   Let $p$ be a prime with $p \neq 2$, and write $\mathbb{Z}_{(p)}$ for the subring [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of those rationals whose denominator is coprime to $p$. Let $H$ be a commutative ring which is a cocommutative Hopf algebra over $\mathbb{Z}_{(p)}$, module-finite and flat over $\mathbb{Z}_{(p)}$, and let $G_H$ denote the monoid `WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)` of $\mathbb{Z}_{(p)}$-algebra homomorphisms $H \to \overline{\mathbb{Q}}$ under convolution; assume $f^p = 1$ for every $f \in G_H$. Let $P$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$ in the sense that $p$ is a nonunit of $P$, and let $I$ be the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $P$ over $\mathbb{Q}$, transported along the inclusion of the decomposition subgroup. Let $N$ be a module over the residue field $k_P$ of $P$, let $\mathrm{act}$ assign to each $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ a $k_P$-linear endomorphism of $N$, and let $F : G_H \to N$ satisfy: $F(fg) = F(f) + F(g)$; for $\sigma \in I$ and $f, g \in G_H$ with $g(h) = \sigma(f(h))$ for all $h \in H$, one has $F(g) = \mathrm{act}_\sigma(F(f))$; and $F(f) \neq 0$ for some $f$. Assume finally that $G_H$ is Galois-simple in the following sense: every submonoid $S \leq G_H$ closed under the operation $f \mapsto \sigma \circ f$ for all $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ equals $\bot$ or $\top$. Then there is an integer $s \geq 1$ such that for every $\pi' \in \overline{\mathbb{Q}}$ with $\pi'^{\,p^s - 1} = p$ there exist a finite set $D \subseteq \mathbb{N}$ with $j < s$ for all $j \in D$ (possibly empty) and a nonzero $w \in N$ with $\mathrm{act}_\sigma(w) = \theta_{\pi'}(\sigma)^{\sum_{j \in D} p^j} \cdot w$ for all $\sigma \in I$, where $\theta_{\pi'}(\sigma) \in k_P$ is [`ValuationSubring.tameCharacter`](def/GaloisRep_TameCharacter.html#L7), namely the residue of $\sigma(\pi')/\pi'$ when that quotient lies in $P$ and $0$ otherwise.
--
--   This is the Galois-simple case of Raynaud's bound on the tame inertia characters occurring in the $\overline{\mathbb{Q}}$-points of a finite flat group scheme of exponent $p$ over the absolutely unramified base $\mathbb{Z}_{(p)}$: the inertia characters are powers of a fundamental character of level $s$ with exponent a sum of distinct $p$-adic digits below $s$. It is the input, via a dévissage to Galois-simple constituents, for the general statement [`HopfAlgebra.exists_inertia_eigenvector_tameCharacter_pow_of_finite_flat`](thm.html#HopfAlgebra.exists_inertia_eigenvector_tameCharacter_pow_of_finite_flat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_inertia_eigenvector_tameCharacter_pow_of_finite_flat_of_galoisSimple.lean

import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HopfAlgebra.exists_inertia_eigenvector_tameCharacter_pow_of_finite_flat_of_galoisSimple
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
      S = ⊥ ∨ S = ⊤) :
    ∃ s : ℕ, 1 ≤ s ∧ ∀ π' : AlgebraicClosure ℚ, π' ^ (p ^ s - 1) = p →
      ∃ D : Finset ℕ, (∀ j ∈ D, j < s) ∧ ∃ w : N, w ≠ 0 ∧
        ∀ σ ∈ P.inertiaSubgroupIn ℚ,
          act σ w = P.tameCharacter π' σ ^ (∑ j ∈ D, p ^ j) • w := by sorry
