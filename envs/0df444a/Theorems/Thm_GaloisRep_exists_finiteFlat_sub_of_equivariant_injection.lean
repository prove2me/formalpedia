-- Prove2me | Theorems.Thm_GaloisRep_exists_finiteFlat_sub_of_equivariant_injection
-- name    : GaloisRep.exists_finiteFlat_sub_of_equivariant_injection
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/c9ab3fd9-9701-5a7c-b21e-a45fd235a976
-- title:
--   Galois-stable subgroups of points arise from finite flat Hopf algebras
-- statement:
--   Fix a natural number $p$ and write $R =$ [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) for the subring of $\mathbb{Q}$ consisting of those rationals whose denominator is coprime to $p$ (so $R = \mathbb{Z}_{(p)}$ for $p$ prime; no primality is assumed). Let $G$ be a commutative ring which is a Hopf algebra over $R$, module-finite and flat over $R$, with cocommutative comultiplication. Let $M$ be an additive abelian group carrying a distributive action of the group $\overline{\mathbb{Q}} \simeq_{\text{alg}[\mathbb{Q}]} \overline{\mathbb{Q}}$ of $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ`, and let $e$ be a bijection from the type of $R$-algebra homomorphisms $G \to \overline{\mathbb{Q}}$, taken in its `WithConv` (convolution) multiplicative structure, to $M$ such that $e(fg) = e(f) + e(g)$ for all $f, g$, and such that whenever $g$ is the homomorphism $x \mapsto \sigma(f(x))$ one has $e(g) = \sigma \cdot e(f)$. Let $N$ be a further abelian group with such a Galois action and $\iota : N \to M$ an injective additive map with $\iota(\sigma \cdot n) = \sigma \cdot \iota(n)$. The conclusion asserts the existence of a commutative ring $H$ with an $R$-Hopf-algebra structure that is module-finite, flat and cocommutative over $R$, together with a bijection $e'$ from the convolution group of $R$-algebra homomorphisms $H \to \overline{\mathbb{Q}}$ to $N$ satisfying the same two conditions: $e'(fg) = e'(f) + e'(g)$, and $e'(g) = \sigma \cdot e'(f)$ whenever $g(x) = \sigma(f(x))$ for all $x \in H$.
--
--   This is the sub-object half of the schematic-closure theorem for finite flat commutative group schemes over the discrete valuation ring $\mathbb{Z}_{(p)}$: a Galois-stable subgroup of the $\overline{\mathbb{Q}}$-points of such a group scheme is again the group of $\overline{\mathbb{Q}}$-points of one, obtained classically as the schematic closure of the corresponding closed subgroup of the generic fibre. It is phrased in the Hopf-algebra-with-points form used by the project's flat-at-$p$ condition on Galois representations, and is invoked to verify the stability of that condition under equivariant injections, for instance in the treatment of Hecke rings and of the finite levels attached to modular forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_exists_finiteFlat_sub_of_equivariant_injection.lean

import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FiniteFlat_ClosureHopf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRep.exists_finiteFlat_sub_of_equivariant_injection (p : ℕ)
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
    (ι : N →+ M) (hι : Function.Injective ι)
    (hι_eq : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (n : N), ι (σ • n) = σ • (ι n)) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) H),
      Module.Finite (GaloisRep.ratLocalizedAt p) H ∧ Module.Flat (GaloisRep.ratLocalizedAt p) H ∧
      Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H ∧
      ∃ e' : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ N,
        (∀ f g, e' (f * g) = e' f + e' g) ∧
        ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
          (∀ x : H, g x = σ (f x)) → e' g = σ • (e' f) := by sorry
