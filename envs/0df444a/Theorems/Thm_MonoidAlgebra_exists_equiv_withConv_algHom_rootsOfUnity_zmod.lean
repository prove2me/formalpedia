-- Prove2me | Theorems.Thm_MonoidAlgebra_exists_equiv_withConv_algHom_rootsOfUnity_zmod
-- name    : MonoidAlgebra.exists_equiv_withConv_algHom_rootsOfUnity_zmod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/11f309b4-08ab-54f0-87fb-5e0d25ce0840
-- title:
--   ̄ K-points of K[ℤ/n] under convolution are μₙ
-- statement:
--   Let $K$ be a field of characteristic zero and let $n$ be a natural number with $n \neq 0$, and write $\overline K$ for `AlgebraicClosure K`. Consider the set of $K$-algebra homomorphisms $K[\mathbb Z/n\mathbb Z] =$ `MonoidAlgebra K (Multiplicative (ZMod n))` $\to \overline K$, equipped by the wrapper `WithConv` with its convolution multiplication (the product of $f$ and $g$ is comultiplication followed by $f \otimes g$ and then multiplication in $\overline K$). The assertion is that there exists a bijection $e\mu$ from this set of convolution-monoid elements onto the subgroup `rootsOfUnity n` $(\overline K)$ of $\overline K^{\times}$ such that: (i) $e\mu(f \cdot g) = e\mu(f)\, e\mu(g)$ for all $f, g$, so $e\mu$ is multiplicative for the convolution product; and (ii) for every $K$-algebra automorphism $\sigma$ of $\overline K$ and all $f, g$ with $g(a) = \sigma(f(a))$ for every $a \in K[\mathbb Z/n\mathbb Z]$, the image of $e\mu(g)$ in $\overline K$ equals $\sigma$ applied to the image of $e\mu(f)$; that is, $e\mu$ is equivariant for post-composition by $\sigma$ on the source and the natural action on roots of unity. Only the existence of such a bijection is asserted, and multiplicativity is stated as a separate clause rather than packaged as a monoid isomorphism.
--
--   This is the computation of the $\overline K$-points of the group scheme $\operatorname{Spec} K[\mathbb Z/n\mathbb Z]$, Cartier dual to the constant group scheme $\mathbb Z/n\mathbb Z$: with the convolution product these points form the group $\mu_n(\overline K)$, Galois-equivariantly. It is used in the construction of the Hopf-algebra description of torsion on a Weierstrass curve in node normal form over a field of characteristic zero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MonoidAlgebra_exists_equiv_withConv_algHom_rootsOfUnity_zmod.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem MonoidAlgebra.exists_equiv_withConv_algHom_rootsOfUnity_zmod
    (K : Type) [Field K] [CharZero K] (n : ℕ) [NeZero n] :
    ∃ eμ : WithConv (MonoidAlgebra K (Multiplicative (ZMod n)) →ₐ[K] AlgebraicClosure K)
        ≃ rootsOfUnity n (AlgebraicClosure K),
      (∀ f g, eμ (f * g) = eμ f * eμ g) ∧
      ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) f g,
        (∀ a, g a = σ (f a))
        → ((eμ g : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)
          = σ ((eμ f : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) := by sorry
