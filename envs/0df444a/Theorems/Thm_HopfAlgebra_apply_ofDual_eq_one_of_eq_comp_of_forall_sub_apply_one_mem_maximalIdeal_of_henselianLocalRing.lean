-- Prove2me | Theorems.Thm_HopfAlgebra_apply_ofDual_eq_one_of_eq_comp_of_forall_sub_apply_one_mem_maximalIdeal_of_henselianLocalRing
-- name    : HopfAlgebra.apply_ofDual_eq_one_of_eq_comp_of_forall_sub_apply_one_mem_maximalIdeal_of_henselianLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/d401cd01-c415-5b65-9f56-e90fdd78fb40
-- title:
--   Trivial Cartier pairing with points factoring through an étale dual
-- statement:
--   Let $R$ be a henselian local commutative ring, and let $A$ and $M$ be commutative rings carrying Hopf algebra structures over $R$ whose comultiplications are cocommutative and which are finite and free as $R$-modules. Let $\pi : A \to M$ be a bialgebra homomorphism over $R$, and assume that the Cartier dual [`CartierDual R M`](def/HopfAlgebra_CartierDual.html#L12), that is the $R$-linear dual of $M$ equipped with its convolution algebra structure, is étale over $R$. Let $f : A \to R$ and $g : M \to R$ be $R$-algebra homomorphisms with $f = g \circ \pi$, and let $\psi : \mathrm{CartierDual}\,R\,A \to R$ be an $R$-algebra homomorphism on the Cartier dual of $A$ such that $\psi(\lambda) - \lambda(1)$ lies in the maximal ideal of $R$ for every $\lambda$ in $\mathrm{CartierDual}\,R\,A$. Then $\psi$ evaluated at the element of $\mathrm{CartierDual}\,R\,A$ given by the underlying $R$-linear map of $f$ equals $1$. No surjectivity of $\pi$ is assumed.
--
--   This is the 'characters are trivial on the multiplicative part' half of the orthogonality of the Cartier pairing: an $R$-point of the Cartier dual congruent to the counit modulo the maximal ideal pairs trivially with any $R$-point coming from a quotient whose dual is étale. It feeds the Cartier-duality computations for $p$-divisible groups, being cited by [`PDivisibleGroup.CartierDuality.pair_eq_one_of_eq_comp_of_etale_cartierDual_of_forall_valuation_sub_counit_lt_one`](thm.html#PDivisibleGroup.CartierDuality.pair_eq_one_of_eq_comp_of_etale_cartierDual_of_forall_valuation_sub_counit_lt_one) and [`PDivisibleGroup.CartierDuality.pair_eq_one_of_forall_valuation_sub_counit_lt_one_of_bijective_tensorProduct_isReduced`](thm.html#PDivisibleGroup.CartierDuality.pair_eq_one_of_forall_valuation_sub_counit_lt_one_of_bijective_tensorProduct_isReduced).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_apply_ofDual_eq_one_of_eq_comp_of_forall_sub_apply_one_mem_maximalIdeal_of_henselianLocalRing.lean

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

universe u v

theorem HopfAlgebra.apply_ofDual_eq_one_of_eq_comp_of_forall_sub_apply_one_mem_maximalIdeal_of_henselianLocalRing
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (A : Type v) [CommRing A] [HopfAlgebra R A] [Coalgebra.IsCocomm R A]
    [Module.Finite R A] [Module.Free R A]

    (M : Type v) [CommRing M] [HopfAlgebra R M] [Coalgebra.IsCocomm R M] [Module.Free R M] [Module.Finite R M]
    (π : A →ₐc[R] M) (hMet : Algebra.Etale R (CartierDual R M))

    (f : A →ₐ[R] R) (g : M →ₐ[R] R) (hf : f = g.comp (π : A →ₐ[R] M))
    (ψ : CartierDual R A →ₐ[R] R)
    (hψ : ∀ lam : CartierDual R A, ψ lam - lam 1 ∈ IsLocalRing.maximalIdeal R) :
    ψ ((CartierDual.ofDual R A) f.toLinearMap) = 1 := by sorry
