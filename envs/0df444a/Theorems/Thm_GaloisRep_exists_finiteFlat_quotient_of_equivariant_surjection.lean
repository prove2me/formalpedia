-- Prove2me | Theorems.Thm_GaloisRep_exists_finiteFlat_quotient_of_equivariant_surjection
-- name    : GaloisRep.exists_finiteFlat_quotient_of_equivariant_surjection
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/d02b39e6-f789-5126-a286-885dd8989da0
-- title:
--   Equivariant quotients of points of finite flat Hopf algebras
-- statement:
--   Let $p$ be a natural number and write $R = \mathbb{Z}_{(p)}$ for the subring [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of those rationals whose denominator is coprime to $p$. Let $G$ be a commutative ring carrying a Hopf algebra structure over $R$ which is module-finite and flat over $R$ and whose comultiplication is cocommutative. Let $M$ be an additive abelian group with a distributive action of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, realised as the $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ`, and let $e$ be a bijection from `WithConv (G →ₐ[R] AlgebraicClosure ℚ)`, the $\overline{\mathbb{Q}}$-points of $G$ with their convolution multiplication, onto $M$ such that $e(f \cdot g) = e(f) + e(g)$, and such that whenever $g$ is the pointwise composite $\sigma \circ f$ on $G$ one has $e(g) = \sigma \cdot e(f)$. Let $N$ be a further abelian group with such a Galois action and let $\pi : M \to N$ be a surjective additive map with $\pi(\sigma \cdot m) = \sigma \cdot \pi(m)$. Then there exists a commutative ring $H$ with an $R$-Hopf algebra structure, module-finite and flat over $R$ and cocommutative, together with a bijection $e'$ from `WithConv (H →ₐ[R] AlgebraicClosure ℚ)` onto $N$ satisfying the same two conditions: convolution goes to addition, and composition with $\sigma$ on points goes to the action of $\sigma$ on $N$.
--
--   This is the quotient half of Raynaud's closure theorem for finite flat commutative group schemes over a discrete valuation ring: a Galois-equivariant quotient of the $\overline{\mathbb{Q}}$-points of a finite flat group scheme over $\mathbb{Z}_{(p)}$ is again the group of points of such a scheme, the model being the schematic closure of the quotient in the generic fibre. It is used in the project as the closure-under-quotients input to the flatness conditions on $p$-adic Galois representations, for instance in the base-change statement [`GaloisRepAdic.isFlatAt_baseChangeAlong_of_finite_residueField`](thm.html#GaloisRepAdic.isFlatAt_baseChangeAlong_of_finite_residueField) and in the flatness of Hecke-ring-valued representations at primes not dividing the level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_exists_finiteFlat_quotient_of_equivariant_surjection.lean

import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FiniteFlat_ClosureHopf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRep.exists_finiteFlat_quotient_of_equivariant_surjection (p : ℕ)
    (G : Type) [CommRing G] [HopfAlgebra (GaloisRep.ratLocalizedAt p) G]
    [Module.Finite (GaloisRep.ratLocalizedAt p) G] [Module.Flat (GaloisRep.ratLocalizedAt p) G]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) G]
    {M : Type} [AddCommGroup M] [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) M]
    (e : WithConv (G →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ M)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (G →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ x : G, g x = σ (f x)) → e g = σ • (e f))
    {N : Type} [AddCommGroup N] [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) N]
    (π : M →+ N) (hπ : Function.Surjective π)
    (hπ_eq : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (m : M), π (σ • m) = σ • (π m)) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) H),
      Module.Finite (GaloisRep.ratLocalizedAt p) H ∧ Module.Flat (GaloisRep.ratLocalizedAt p) H ∧
      Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H ∧
      ∃ e' : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ N,
        (∀ f g, e' (f * g) = e' f + e' g) ∧
        ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
          (∀ x : H, g x = σ (f x)) → e' g = σ • (e' f) := by sorry
