-- Prove2me | Theorems.Thm_HopfAlgebra_exists_inertiaStable_simple_step_of_map_ne_zero
-- name    : HopfAlgebra.exists_inertiaStable_simple_step_of_map_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/76439004-a0f0-5fa6-8b89-7ce3a74d7f59
-- title:
--   Inertia-simple step carrying a nonzero additive functional
-- statement:
--   Let $p$ be a prime and let $H$ be a commutative ring carrying a Hopf algebra structure over the subring $\mathbb{Z}_{(p)} =$ [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of the rationals whose denominator is coprime to $p$, with $H$ finite and flat as a $\mathbb{Z}_{(p)}$-module and cocommutative as a coalgebra. Write $M$ for the set of $\mathbb{Z}_{(p)}$-algebra homomorphisms $H \to \overline{\mathbb{Q}}$ equipped, through `WithConv`, with its convolution monoid structure, and assume $f^p = 1$ for every $f \in M$. Let $P$ be a valuation subring of $\overline{\mathbb{Q}}$, and call a submonoid $S \le M$ inertia-stable if for every $\sigma$ in `P.inertiaSubgroupIn ℚ` (the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $P$ under the inclusion of the decomposition subgroup), every $f \in S$ and every $g \in M$ with $g(h) = \sigma(f(h))$ for all $h \in H$, one has $g \in S$. Let $N$ be an additive commutative group and $F : M \to N$ satisfy $F(fg) = F(f) + F(g)$, and let $K_0 \le M$ be an inertia-stable submonoid on which $F$ is not identically zero. Then there exist submonoids $K \le K' \le K_0$, both inertia-stable, such that every inertia-stable submonoid $S$ with $K \le S \le K'$ equals $K$ or $K'$, such that $F$ vanishes on $K$ while $F$ is nonzero at some element of $K'$, and such that $\#K' = p^{s}\,\#K$ for some integer $s \ge 1$. The index assertion is thus only that $\#K'/\#K$ is a positive power of $p$, not that it equals $p$.
--
--   This is the elementary Jordan–Hölder step used in the treatment of Raynaud's theorem on finite flat group schemes of type $(p,\dots,p)$: one extracts from an inertia-stable group of $\overline{\mathbb{Q}}$-points a minimal inertia-stable piece on which a given additive functional survives, together with an inertia-simple step below it. It feeds the tame-character eigenvector statement [`HopfAlgebra.exists_inertia_eigenvector_tameCharacter_pow_of_finite_flat_of_galoisSimple_of_exists_reductionKernel_map_ne_zero`](thm.html#HopfAlgebra.exists_inertia_eigenvector_tameCharacter_pow_of_finite_flat_of_galoisSimple_of_exists_reductionKernel_map_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_inertiaStable_simple_step_of_map_ne_zero.lean

import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HopfAlgebra.exists_inertiaStable_simple_step_of_map_ne_zero
    {p : ℕ} (hp : p.Prime)
    {H : Type} [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
    (hMp : ∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ), f ^ p = 1)
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (N : Type) [AddCommGroup N]
    (F : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) → N)
    (hFmul : ∀ f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
      F (f * g) = F f + F g)
    (K₀ : Submonoid (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)))
    (hK₀ : (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K₀,
      ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        (∀ h : H, g h = σ (f h)) → g ∈ K₀))
    (hFK₀ : ∃ f ∈ K₀, F f ≠ 0) :
    ∃ K K' : Submonoid (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      K ≤ K' ∧ K' ≤ K₀ ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K,
        ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
          (∀ h : H, g h = σ (f h)) → g ∈ K) ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K',
        ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
          (∀ h : H, g h = σ (f h)) → g ∈ K') ∧
      (∀ S : Submonoid (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
        K ≤ S → S ≤ K' →
        (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ S,
          ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
            (∀ h : H, g h = σ (f h)) → g ∈ S) →
        S = K ∨ S = K') ∧
      (∀ f ∈ K, F f = 0) ∧ (∃ f ∈ K', F f ≠ 0) ∧
      ∃ s : ℕ, 1 ≤ s ∧ Nat.card K' = p ^ s * Nat.card K := by sorry
