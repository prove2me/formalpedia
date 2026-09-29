-- Prove2me | Theorems.Thm_HopfAlgebra_exists_withConv_equiv_rootsOfUnity_of_comul_gens_quadraticTwist
-- name    : HopfAlgebra.exists_withConv_equiv_rootsOfUnity_of_comul_gens_quadraticTwist
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/4f8454aa-56cb-577a-b223-e1cb6dbce403
-- title:
--   Points of a norm-one torus Hopf algebra as μₙ
-- statement:
--   Let $K$ be a field of characteristic zero, let $c \in K$ be non-zero and not a square in $K$, let $n$ be a prime, and fix $\delta$ in an algebraic closure $\overline K$ of $K$ with $\delta^2 = c$ (the image of $c$ in $\overline K$). Let $A$ be a commutative ring which is a $K$-Hopf algebra, and let $u, v \in A$ satisfy the norm-one relation $u^2 - c v^2 = 1$ together with the comultiplication formulas $\Delta(u) = u \otimes u + c\,(v \otimes v)$ and $\Delta(v) = u \otimes v + v \otimes u$. Assume further that $(f(u) + f(v)\delta)^n = 1$ for every $K$-algebra homomorphism $f : A \to \overline K$, and that conversely, for all $w, z \in \overline K$ with $w^2 - c z^2 = 1$ and $(w + z\delta)^n = 1$, there is a unique $K$-algebra homomorphism $f : A \to \overline K$ with $f(u) = w$ and $f(v) = z$. The conclusion asserts the existence of a bijection $e_\mu$ from $\operatorname{Hom}_{K\text{-alg}}(A, \overline K)$, regarded via `WithConv` as a monoid under the convolution product coming from the Hopf structure, onto the group $\mu_n(\overline K)$ of $n$-th roots of unity, such that $e_\mu(f \ast g) = e_\mu(f)\,e_\mu(g)$ for all $f, g$, and such that for every $\sigma \in \operatorname{Aut}_K(\overline K)$ and all $f, g$ with $g = \sigma \circ f$ pointwise on $A$: if $\sigma\delta = \delta$ then $e_\mu(g) = \sigma(e_\mu(f))$, and if $\sigma\delta = -\delta$ then $e_\mu(g)\cdot\sigma(e_\mu(f)) = 1$, the roots of unity being compared through their images in $\overline K$.
--
--   This is the points half of the identification of the $\overline K$-points of the $n$-torsion of the norm-one torus of $K(\sqrt c)$ with $\mu_n$ carrying the quadratically twisted Galois action; the existential conclusion records a multiplicative bijection with that equivariance without naming $f \mapsto f(u) + f(v)\delta$ explicitly. It is used by [`HopfAlgebra.exists_withConv_algHom_equiv_rootsOfUnity_quadraticTwist`](thm.html#HopfAlgebra.exists_withConv_algHom_equiv_rootsOfUnity_quadraticTwist).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_withConv_equiv_rootsOfUnity_of_comul_gens_quadraticTwist.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct in

theorem HopfAlgebra.exists_withConv_equiv_rootsOfUnity_of_comul_gens_quadraticTwist
    (K : Type) [Field K] [CharZero K] (c : K) (hc : c ≠ 0) (hnsq : ¬ IsSquare c)
    (n : ℕ) [Fact n.Prime]
    (δ : AlgebraicClosure K) (hδ : δ * δ = algebraMap K (AlgebraicClosure K) c)
    (A : Type) [CommRing A] [HopfAlgebra K A] (u v : A)
    (hrel : u ^ 2 - algebraMap K A c * v ^ 2 = 1)
    (hcu : Coalgebra.comul (R := K) u = u ⊗ₜ[K] u + c • (v ⊗ₜ[K] v))
    (hcv : Coalgebra.comul (R := K) v = u ⊗ₜ[K] v + v ⊗ₜ[K] u)
    (hn : ∀ f : A →ₐ[K] AlgebraicClosure K, (f u + f v * δ) ^ n = 1)
    (hlift : ∀ (w z : AlgebraicClosure K),
      w ^ 2 - algebraMap K (AlgebraicClosure K) c * z ^ 2 = 1 →
      (w + z * δ) ^ n = 1 →
      ∃! f : A →ₐ[K] AlgebraicClosure K, f u = w ∧ f v = z) :
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
