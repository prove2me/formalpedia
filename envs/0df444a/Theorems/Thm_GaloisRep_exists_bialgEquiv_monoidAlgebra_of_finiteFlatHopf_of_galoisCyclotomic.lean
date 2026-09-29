-- Prove2me | Theorems.Thm_GaloisRep_exists_bialgEquiv_monoidAlgebra_of_finiteFlatHopf_of_galoisCyclotomic
-- name    : GaloisRep.exists_bialgEquiv_monoidAlgebra_of_finiteFlatHopf_of_galoisCyclotomic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/d9144ff9-6649-5786-b8b5-1882571b46c2
-- title:
--   Cyclotomic finite flat Hopf algebras over ℤ_{(q)} are monoid algebras
-- statement:
--   Let $q$ be a prime with $q \neq 2$ and write $R = \mathbb{Z}_{(q)}$ for [`GaloisRep.ratLocalizedAt q`](def/GaloisRep_Flat.html#L8), the subring of $\mathbb{Q}$ consisting of those rationals whose denominator is coprime to $q$. Let $H$ be a commutative ring carrying a Hopf algebra structure over $R$ that is finite and free as an $R$-module and whose comultiplication is cocommutative. Let $M$ be a finite additive abelian group with a distributive action of $G = \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, realised as the $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ`, and let $e$ be a bijection from `WithConv (H →ₐ[R] AlgebraicClosure ℚ)`, the $\overline{\mathbb{Q}}$-points of $H$ under convolution, onto $M$ which turns convolution into addition ($e(f g) = e f + e g$) and is Galois-equivariant in the sense that $e g = \sigma \cdot e f$ whenever $g x = \sigma(f x)$ for all $x \in H$. Assume $q^k$ annihilates $M$ for some $k$, that $n : G \to \mathbb{N}$ satisfies $\sigma\zeta = \zeta^{n(\sigma)}$ for every $\zeta \in \overline{\mathbb{Q}}$ with $\zeta^{q^k} = 1$, that $\sigma \cdot m = n(\sigma) \, m$ for all $\sigma \in G$, $m \in M$, and that $\#M = \mathrm{rank}_R H$. Then there exists an $R$-bialgebra equivalence $\varphi$ from $H$ to the monoid algebra over $R$ on `WithConv (CartierDual R H →ₐ[R] AlgebraicClosure ℚ)`, the convolution monoid of $\overline{\mathbb{Q}}$-points of the Cartier dual [`CartierDual R H`](def/HopfAlgebra_CartierDual.html#L12) $= \mathrm{Hom}_R(H, R)$, such that for every such point $\psi$ and every $\theta \in \mathrm{Hom}_R(H,R)$ the value $\theta(\varphi^{-1}(\text{single } \psi\, 1)) \in R$ has image $\psi(\theta)$ in $\overline{\mathbb{Q}}$.
--
--   This is the multiplicative-type half of the Oort–Tate/Raynaud classification of finite flat commutative group schemes in the situation relevant to the $q$-torsion layers over $\mathbb{Z}_{(q)}$ with $q$ odd: a group scheme $\mathrm{Spec}\,H$ whose geometric points carry the cyclotomic Galois action and whose order matches the rank of $H$ is the Cartier dual of a constant group scheme, so $H$ is the group (monoid) algebra on the points of its Cartier dual. It is used by [`HopfAlgebra.nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_ratLocalizedAt_eq_of_convPow_of_ne_two`](thm.html#HopfAlgebra.nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_ratLocalizedAt_eq_of_convPow_of_ne_two), and rests on the corresponding statement for trivial Galois action together with Cartier biduality.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_exists_bialgEquiv_monoidAlgebra_of_finiteFlatHopf_of_galoisCyclotomic.lean

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRep.exists_bialgEquiv_monoidAlgebra_of_finiteFlatHopf_of_galoisCyclotomic
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt q) H]
    [Module.Finite (GaloisRep.ratLocalizedAt q) H] [Module.Free (GaloisRep.ratLocalizedAt q) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt q) H]
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
    ∃ φ : H ≃ₐc[GaloisRep.ratLocalizedAt q]
        MonoidAlgebra (GaloisRep.ratLocalizedAt q)
          (WithConv (CartierDual (GaloisRep.ratLocalizedAt q) H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ)),
      ∀ (ψ : WithConv (CartierDual (GaloisRep.ratLocalizedAt q) H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ))
        (θ : CartierDual (GaloisRep.ratLocalizedAt q) H),
        algebraMap (GaloisRep.ratLocalizedAt q) (AlgebraicClosure ℚ) (θ (φ.symm (MonoidAlgebra.single ψ 1))) = ψ θ := by sorry
