-- Prove2me | Theorems.Thm_HopfAlgebra_exists_algEquiv_pi_of_injective_points_of_finrank_eq
-- name    : HopfAlgebra.exists_algEquiv_pi_of_injective_points_of_finrank_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/ab97e713-43c1-5433-ba99-78b45419ec15
-- title:
--   Full ℓ-power torsion points force a constant group scheme
-- statement:
--   Let $O$ be a commutative domain which is a discrete valuation ring, and let $\ell$ be a prime number with $\ell \neq 2$ whose image in $O$ is irreducible, so that $\ell$ is a uniformiser of $O$. Let $H$ be a commutative ring carrying the structure of a Hopf algebra over $O$ whose comultiplication is cocommutative, and which is finite and flat as an $O$-module. Write $H \to_{\mathrm{alg}} O$ for the $O$-algebra maps out of $H$, equipped with the convolution monoid structure `WithConv`. Assume there is a natural number $k$ such that $x^{\ell^{k}} = 1$ for every such $x$, and that every such $x$ has a two-sided convolution inverse. Let $\iota$ be a finite type and $y : \iota \to H \to_{\mathrm{alg}} O$ an injective family of $O$-algebra maps with $\operatorname{finrank}_O H = \#\iota$. Then there is an isomorphism of $O$-algebras $\varphi : H \simeq (\iota \to O)$ whose components are the given points: $\varphi(a)(i) = y_i(a)$ for all $a \in H$ and $i \in \iota$.
--
--   In geometric terms: a finite flat commutative and cocommutative group scheme $G = \operatorname{Spec} H$ over a discrete valuation ring in which an odd prime $\ell$ is a uniformiser, whose group of $O$-points is killed by a power of $\ell$ and has at least $\operatorname{rank}_O H$ distinct elements, is the constant group scheme on those points, evaluation being the comparison map. It is used in the recognition of such group schemes arising from Galois representations, via [`GaloisRep.exists_algEquiv_pi_of_finiteFlatHopf_of_galoisTrivial`](thm.html#GaloisRep.exists_algEquiv_pi_of_finiteFlatHopf_of_galoisTrivial), and rests on the triviality of the kernel of reduction on $\ell$-power torsion points recorded in [`HopfAlgebra.point_eq_one_of_pow_prime_pow_eq_one_of_sub_counit_mem_maximalIdeal`](thm.html#HopfAlgebra.point_eq_one_of_pow_prime_pow_eq_one_of_sub_counit_mem_maximalIdeal).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_algEquiv_pi_of_injective_points_of_finrank_eq.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HopfAlgebra.exists_algEquiv_pi_of_injective_points_of_finrank_eq
    (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hunif : Irreducible (ℓ : O))
    (H : Type*) [CommRing H] [HopfAlgebra O H] [Module.Finite O H] [Module.Flat O H] [Coalgebra.IsCocomm O H]
    (k : ℕ) (htors : ∀ x : WithConv (H →ₐ[O] O), x ^ ℓ ^ k = 1)
    (hinv : ∀ x : WithConv (H →ₐ[O] O), ∃ z : WithConv (H →ₐ[O] O), x * z = 1 ∧ z * x = 1)
    {ι : Type*} [Fintype ι] (y : ι → WithConv (H →ₐ[O] O)) (hy : Function.Injective y)
    (hrank : Module.finrank O H = Fintype.card ι) :
    ∃ φ : H ≃ₐ[O] (ι → O), ∀ (a : H) (i : ι), φ a i = y i a := by sorry
