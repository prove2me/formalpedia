-- Prove2me | Theorems.Thm_HopfAlgebra_exists_withConv_equiv_padic_of_withConv_equiv_algebraicClosure
-- name    : HopfAlgebra.exists_withConv_equiv_padic_of_withConv_equiv_algebraicClosure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/d609cd03-be89-593a-a813-64a02de81326
-- title:
--   Galois module of ℚ̄-points transfers to ℚ̄ₚ-points
-- statement:
--   Let $p$ be a prime, let $A$ be a commutative ring carrying a Hopf algebra structure over $\mathbb Q$ which is finite as a $\mathbb Q$-module, and let $N$ be an additive commutative group equipped with a distributive multiplicative action of $\mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q}) = \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$, where $\overline{\mathbb Q}$ is `AlgebraicClosure ℚ`. Suppose given a bijection $e_A$ from `WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ)`, the set of $\mathbb Q$-algebra homomorphisms $A \to \overline{\mathbb Q}$ with its convolution monoid structure, onto $N$, such that $e_A(f \cdot g) = e_A(f) + e_A(g)$ for all $f, g$ (convolution on the left, addition in $N$ on the right), and such that for every $\sigma \in \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ and all points $f, g$ with $g(a) = \sigma(f(a))$ for all $a \in A$ one has $e_A(g) = \sigma \cdot e_A(f)$. Then there exists a bijection $e_{A,p}$ from `WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ_[p])` onto the same group $N$ satisfying $e_{A,p}(f \cdot g) = e_{A,p}(f) + e_{A,p}(g)$ and, for every $\sigma \in \mathrm{Gal}(\overline{\mathbb Q}_p/\mathbb Q_p)$ and all $f, g$ with $g(a) = \sigma(f(a))$ for all $a \in A$, the equivariance $e_{A,p}(g) = (\mathtt{localGaloisToGlobal}\ p\ \sigma) \cdot e_{A,p}(f)$, where [`localGaloisToGlobal p`](def/GaloisRep_CompletionBridge.html#L41) is the monoid homomorphism sending $\sigma$ to its restriction of scalars to $\mathbb Q$ followed by restriction to the normal subextension $\overline{\mathbb Q}$.
--
--   This is the comparison of the global and $p$-adic point sets of a finite $\mathbb Q$-Hopf algebra: the convolution monoid of $\overline{\mathbb Q}$-points and that of $\overline{\mathbb Q}_p$-points carry the same additive structure, the local Galois group acting through restriction along a fixed embedding $\overline{\mathbb Q} \hookrightarrow \overline{\mathbb Q}_p$. It is used in the construction of the local Galois module attached to a finite flat group scheme from its global counterpart, being cited by [`GaloisRep.exists_hopfAlgebra_withConv_equiv_of_ordinary_of_unitKummer_decomposition`](thm.html#GaloisRep.exists_hopfAlgebra_withConv_equiv_of_ordinary_of_unitKummer_decomposition).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_withConv_equiv_padic_of_withConv_equiv_algebraicClosure.lean

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem HopfAlgebra.exists_withConv_equiv_padic_of_withConv_equiv_algebraicClosure
    (p : ℕ) [Fact p.Prime]
    (A : Type) [CommRing A] [HopfAlgebra ℚ A] (hAfin : Module.Finite ℚ A)
    {N : Type} [AddCommGroup N] [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) N]
    (eA : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ) ≃ N)
    (heA_add : ∀ f g, eA (f * g) = eA f + eA g)
    (heA_act : ∀ (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (f g : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ)),
      (∀ a : A, g a = σ (f a)) → eA g = σ • (eA f)) :
    ∃ eAp : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ_[p]) ≃ N,
      (∀ f g, eAp (f * g) = eAp f + eAp g) ∧
      ∀ (σ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])) (f g : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ_[p])),
        (∀ a : A, g a = σ (f a)) → eAp g = (localGaloisToGlobal p σ) • (eAp f) := by sorry
