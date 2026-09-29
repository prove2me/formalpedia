-- Prove2me | Theorems.Thm_GaloisRep_cartierDual_points_of_galoisCyclotomic
-- name    : GaloisRep.cartierDual_points_of_galoisCyclotomic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/27b5978b-a7a6-5223-a183-b163eeb59376
-- title:
--   Points of the Cartier dual of a multiplicative-type Hopf algebra
-- statement:
--   Let $q$ be a prime and let $R = \mathbb{Z}_{(q)}$ be the subring [`GaloisRep.ratLocalizedAt q`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of the rationals whose denominator is coprime to $q$. Let $H$ be a commutative ring carrying a Hopf algebra structure over $R$ which is finite and free as an $R$-module, and let $M$ be a finite additive commutative group equipped with a distributive action of the group $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ`. Assume given a bijection $e$ from the set of $R$-algebra homomorphisms $H \to \overline{\mathbb{Q}}$, viewed with its convolution monoid structure, onto $M$, such that $e(f * g) = e(f) + e(g)$ for the convolution product, and such that whenever $g$ is the pointwise composite $\sigma \circ f$ one has $e(g) = \sigma \cdot e(f)$. Assume further: a natural number $k$ with $q^k \cdot m = 0$ for all $m \in M$; a function $n$ from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ to $\mathbb{N}$ with $\sigma(\zeta) = \zeta^{n(\sigma)}$ for every $\zeta \in \overline{\mathbb{Q}}$ satisfying $\zeta^{q^k} = 1$, and with $\sigma \cdot m = n(\sigma) \cdot m$ for all $m \in M$; and $\#M = \mathrm{rank}_R H$. Then, writing $H^{\vee}$ for the Cartier dual [`CartierDual`](def/HopfAlgebra_CartierDual.html#L12) of $H$, namely the $R$-linear dual $\mathrm{Hom}_R(H,R)$ with its bialgebra structure: (i) for every $\sigma$, every $R$-algebra homomorphism $\psi : H^{\vee} \to \overline{\mathbb{Q}}$ and every $\varphi \in H^{\vee}$ one has $\sigma(\psi(\varphi)) = \psi(\varphi)$; (ii) every such $\psi$ satisfies $\psi^{q^k} = 1$ in the convolution monoid; (iii) the number of such $\psi$ equals $\mathrm{rank}_R H$.
--
--   This is the points-level form, over the generic fibre, of the statement that the Cartier dual of a finite flat group scheme of multiplicative type is étale with trivial Galois action: the hypotheses say that the $\overline{\mathbb{Q}}$-points of $H$ form a finite abelian $q^k$-torsion group of order the rank of $H$ on which Galois acts through the cyclotomic character, and the conclusion records the three properties of the point monoid of $H^{\vee}$ (Galois-triviality, $q^k$-torsion, rank-many points). It feeds the identification of such Hopf algebras with monoid algebras in [`GaloisRep.exists_bialgEquiv_monoidAlgebra_of_finiteFlatHopf_of_galoisCyclotomic`](thm.html#GaloisRep.exists_bialgEquiv_monoidAlgebra_of_finiteFlatHopf_of_galoisCyclotomic) and [`HopfAlgebra.nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_ratLocalizedAt_eq_of_convPow_of_ne_two`](thm.html#HopfAlgebra.nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_ratLocalizedAt_eq_of_convPow_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_cartierDual_points_of_galoisCyclotomic.lean

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRep.cartierDual_points_of_galoisCyclotomic
    (q : ℕ) [Fact q.Prime]
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt q) H]
    [Module.Finite (GaloisRep.ratLocalizedAt q) H] [Module.Free (GaloisRep.ratLocalizedAt q) H]
    {M : Type} [AddCommGroup M] [Finite M]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) M]
    (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) ≃ M)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ)),
      (∀ x : H, g x = σ (f x)) → e g = σ • (e f))
    (k : ℕ) (htors : ∀ m : M, q ^ k • m = 0)
    (n : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ℕ)
    (hn : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (ζ : AlgebraicClosure ℚ),
      ζ ^ q ^ k = 1 → σ ζ = ζ ^ n σ)
    (hcyc : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (m : M), σ • m = n σ • m)
    (hcard : Nat.card M = Module.finrank (GaloisRep.ratLocalizedAt q) H) :
    (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (ψ : WithConv (CartierDual (GaloisRep.ratLocalizedAt q) H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ))
        (φ : CartierDual (GaloisRep.ratLocalizedAt q) H), σ (ψ φ) = ψ φ) ∧
    (∀ ψ : WithConv (CartierDual (GaloisRep.ratLocalizedAt q) H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ),
        ψ ^ q ^ k = 1) ∧
    Nat.card (WithConv (CartierDual (GaloisRep.ratLocalizedAt q) H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ))
      = Module.finrank (GaloisRep.ratLocalizedAt q) H := by sorry
