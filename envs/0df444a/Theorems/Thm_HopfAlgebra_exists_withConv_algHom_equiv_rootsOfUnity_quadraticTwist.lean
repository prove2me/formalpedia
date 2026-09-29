-- Prove2me | Theorems.Thm_HopfAlgebra_exists_withConv_algHom_equiv_rootsOfUnity_quadraticTwist
-- name    : HopfAlgebra.exists_withConv_algHom_equiv_rootsOfUnity_quadraticTwist
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/34aee1ba-43df-5e64-ab04-cd1e4571ec85
-- title:
--   Finite Hopf algebra with twisted μₙ-points
-- statement:
--   Let $K$ be a field of characteristic zero, let $c \in K$ with $c \neq 0$ and $c$ not a square in $K$, let $n$ be a natural number that is prime (as a typeclass fact), and fix $\delta$ in the algebraic closure $\overline K$ with $\delta \cdot \delta = c$ (the image of $c$ under the structure map $K \to \overline K$). The assertion is the existence of a type $A$ together with commutative ring and $K$-Hopf algebra structures such that: $A$ is finite as a $K$-module; its comultiplication is cocommutative; and there is a bijection $e_\mu$ from the set of $K$-algebra homomorphisms $A \to \overline K$, regarded as a monoid under the convolution product coming from the Hopf structure, onto the group $\mu_n(\overline K)$ of $n$-th roots of unity in $\overline K$ (a subgroup of $\overline K^{\times}$), with the two properties: $e_\mu(f \cdot g) = e_\mu(f) \cdot e_\mu(g)$ for all $f, g$; and for every $K$-algebra automorphism $\sigma$ of $\overline K$ and all $f, g$ with $g(a) = \sigma(f(a))$ for every $a \in A$, one has $e_\mu(g) = \sigma(e_\mu(f))$ whenever $\sigma(\delta) = \delta$, and $e_\mu(g) \cdot \sigma(e_\mu(f)) = 1$ whenever $\sigma(\delta) = -\delta$ (the values being compared inside $\overline K$ after passing through $\overline K^{\times}$).
--
--   This records the coordinate Hopf algebra of the quadratic twist of $\mu_n$ by $K(\sqrt{c})/K$, equivalently the $n$-torsion of the norm-one torus of that quadratic extension: its $\overline K$-points form a cyclic group of order $n$ on which the Galois action agrees with the cyclotomic one up to the quadratic character of $K(\sqrt c)/K$. It is used in the construction of the $n$-torsion Hopf algebra of a Weierstrass curve in node normal form over a characteristic-zero field whose node parameter is a non-square, i.e. for a non-split multiplicative fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_withConv_algHom_equiv_rootsOfUnity_quadraticTwist.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HopfAlgebra.exists_withConv_algHom_equiv_rootsOfUnity_quadraticTwist
    (K : Type) [Field K] [CharZero K] (c : K) (hc : c ≠ 0) (hnsq : ¬ IsSquare c)
    (n : ℕ) [Fact n.Prime]
    (δ : AlgebraicClosure K) (hδ : δ * δ = algebraMap K (AlgebraicClosure K) c) :
    ∃ (A : Type) (_ : CommRing A) (_ : HopfAlgebra K A),
      Module.Finite K A ∧ Coalgebra.IsCocomm K A ∧
      ∃ eμ : WithConv (A →ₐ[K] AlgebraicClosure K) ≃ rootsOfUnity n (AlgebraicClosure K),
        (∀ f g, eμ (f * g) = eμ f * eμ g) ∧
        ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
          (f g : WithConv (A →ₐ[K] AlgebraicClosure K)),
          (∀ a : A, g a = σ (f a)) →
          (σ δ = δ →
            ((eμ g : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)
            = σ ((eμ f : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)) ∧
          (σ δ = -δ →
            ((eμ g : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)
            * σ ((eμ f : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) = 1) := by sorry
