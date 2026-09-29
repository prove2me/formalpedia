-- Prove2me | Theorems.Thm_HopfAlgebra_exists_inertia_eigenvector_tameCharacter_pow_of_finite_flat
-- name    : HopfAlgebra.exists_inertia_eigenvector_tameCharacter_pow_of_finite_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/ecb9723e-0df7-5780-951b-4c508280392b
-- title:
--   Inertia eigenvector with tame character of p-adic digits 0,1
-- statement:
--   Let $p$ be an odd prime, and let $H$ be a commutative ring that is a cocommutative Hopf algebra over the subring $\mathbb{Z}_{(p)} \subset \mathbb{Q}$ of rationals whose denominator is coprime to $p$ ([`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8)), finite and flat as a module over that subring. Assume every element of the convolution monoid `WithConv` of $\mathbb{Z}_{(p)}$-algebra homomorphisms $H \to \overline{\mathbb{Q}}$ satisfies $f^{p} = 1$. Let $P$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ lying in the non-units of $P$, let $N$ be a vector space over the residue field of $P$, let $\mathrm{act}$ assign to each $\sigma \in \operatorname{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ a residue-field-linear endomorphism of $N$, and let $F$ be a map from the points of $H$ to $N$ with $F(fg) = F(f) + F(g)$, satisfying, for every $\sigma$ in the image in $\operatorname{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ of the inertia subgroup of $P$ inside its decomposition subgroup, $F(g) = \mathrm{act}(\sigma)(F(f))$ whenever $g(h) = \sigma(f(h))$ for all $h \in H$; assume $F$ is not identically zero. The conclusion asserts the existence of $s \geq 1$ such that for every $\pi' \in \overline{\mathbb{Q}}$ with $\pi'^{\,p^{s}-1} = p$ there are a finite set $D$ of natural numbers, all $< s$, and a non-zero $w \in N$ with $\mathrm{act}(\sigma)(w) = \theta_{\pi'}(\sigma)^{\sum_{j \in D} p^{j}} \cdot w$ for all such inertia elements $\sigma$, where $\theta_{\pi'}(\sigma)$ is the residue of $\sigma(\pi')/\pi'$ if that quotient lies in $P$ and $0$ otherwise.
--
--   This is Raynaud's theorem on finite flat group schemes killed by $p$ over an unramified base, in the form used downstream: the tame inertia character of the residual representation is a power of a fundamental character whose exponent has $p$-adic digits $0$ and $1$. It is cited by [`GaloisRepAdic.exists_inertia_eigenvector_tameCharacter_of_isFlatAt`](thm.html#GaloisRepAdic.exists_inertia_eigenvector_tameCharacter_of_isFlatAt), which supplies the Hopf algebra, its finiteness, flatness and cocommutativity, and the identification of its points with the residual representation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_inertia_eigenvector_tameCharacter_pow_of_finite_flat.lean

import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HopfAlgebra.exists_inertia_eigenvector_tameCharacter_pow_of_finite_flat
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
    (hFne : ∃ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ), F f ≠ 0) :
    ∃ s : ℕ, 1 ≤ s ∧ ∀ π' : AlgebraicClosure ℚ, π' ^ (p ^ s - 1) = p →
      ∃ D : Finset ℕ, (∀ j ∈ D, j < s) ∧ ∃ w : N, w ≠ 0 ∧
        ∀ σ ∈ P.inertiaSubgroupIn ℚ,
          act σ w = P.tameCharacter π' σ ^ (∑ j ∈ D, p ^ j) • w := by sorry
