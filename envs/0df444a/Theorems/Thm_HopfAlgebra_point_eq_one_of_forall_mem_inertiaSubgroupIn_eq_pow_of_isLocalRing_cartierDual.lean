-- Prove2me | Theorems.Thm_HopfAlgebra_point_eq_one_of_forall_mem_inertiaSubgroupIn_eq_pow_of_isLocalRing_cartierDual
-- name    : HopfAlgebra.point_eq_one_of_forall_mem_inertiaSubgroupIn_eq_pow_of_isLocalRing_cartierDual
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/923789b2-9702-5e10-9a0b-3158e62001b1
-- title:
--   No μₚ-type point when the Cartier dual is local
-- statement:
--   Let $p$ be a prime with $p \neq 2$, and write $R = \mathbb{Z}_{(p)}$ for the subring [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of the rationals whose denominator is coprime to $p$. Let $H$ be a commutative ring carrying a Hopf algebra structure over $R$ which is finite and free as an $R$-module and whose comultiplication is cocommutative, and assume that the Cartier dual $\mathrm{Hom}_R(H,R)$, with its induced ring structure, is a local ring. Let $P$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` lying over $p$, in the sense that the image of $p$ is a non-unit of $P$, and let $I_P$ denote the inertia subgroup of $P$ over $\mathbb{Q}$, i.e. the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of the decomposition group of $P$. Let $n$ assign a natural number to each automorphism $\sigma$ of $\overline{\mathbb{Q}}$ over $\mathbb{Q}$ in such a way that $\sigma\zeta = \zeta^{n(\sigma)}$ for every $\zeta \in \overline{\mathbb{Q}}$ with $\zeta^p = 1$; thus $n$ realises the mod $p$ cyclotomic character on the whole Galois group. Let $f$ be an $R$-algebra homomorphism $H \to \overline{\mathbb{Q}}$, regarded as an element of the group `WithConv` of such homomorphisms under convolution, and suppose $f^p = 1$ there. Suppose further that for every $\sigma \in I_P$ and every algebra homomorphism $g : H \to \overline{\mathbb{Q}}$ with $g(h) = \sigma(f(h))$ for all $h \in H$ one has $g = f^{n(\sigma)}$ in the convolution group. Then $f = 1$.
--
--   In geometric language: a finite flat commutative group scheme over $\mathbb{Z}_{(p)}$, $p$ odd, whose Cartier dual is connected admits no $\overline{\mathbb{Q}}$-point of order dividing $p$ on which inertia at $p$ acts through the mod $p$ cyclotomic character, i.e. no line of $\mu_p$-type. It is used in the local analysis at $p$ of the Galois representations attached to cusp forms, entering [`CuspForm.exists_galoisRepAdic_inertia_eigenvector_tameCharacter_of_not_isUnit_heckeT_of_ne_two`](thm.html#CuspForm.exists_galoisRepAdic_inertia_eigenvector_tameCharacter_of_not_isUnit_heckeT_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_point_eq_one_of_forall_mem_inertiaSubgroupIn_eq_pow_of_isLocalRing_cartierDual.lean

import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_HopfAlgebra_CartierDual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HopfAlgebra.point_eq_one_of_forall_mem_inertiaSubgroupIn_eq_pow_of_isLocalRing_cartierDual
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Free (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
    [IsLocalRing (CartierDual (GaloisRep.ratLocalizedAt p) H)]
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (n : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ℕ)
    (hn : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (ζ : AlgebraicClosure ℚ),
      ζ ^ p = 1 → σ ζ = ζ ^ n σ)
    (f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) (hfp : f ^ p = 1)
    (hf : ∀ σ ∈ P.inertiaSubgroupIn ℚ,
      ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        (∀ h : H, g h = σ (f h)) → g = f ^ n σ) :
    f = 1 := by sorry
