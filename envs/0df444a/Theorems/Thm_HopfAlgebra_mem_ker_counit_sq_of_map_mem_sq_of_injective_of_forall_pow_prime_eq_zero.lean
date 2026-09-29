-- Prove2me | Theorems.Thm_HopfAlgebra_mem_ker_counit_sq_of_map_mem_sq_of_injective_of_forall_pow_prime_eq_zero
-- name    : HopfAlgebra.mem_ker_counit_sq_of_map_mem_sq_of_injective_of_forall_pow_prime_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/c9fa94d7-5758-519a-bc12-4969f731d8b7
-- title:
--   Injectivity of cotangent maps for height-one Hopf algebras
-- statement:
--   Let $k$ be a field of characteristic $p$ for a prime $p$, and let $D$ be a commutative ring equipped with a Hopf algebra structure over $k$ which is finite as a $k$-module, satisfying the height-one condition that $x^p = 0$ for every $x \in D$ with $\varepsilon_D(x) = 0$, where $\varepsilon_D$ denotes the counit of the coalgebra structure. Let $C$ be a commutative ring with a bialgebra structure over $k$, and let $\iota : C \to D$ be a morphism of $k$-bialgebras (a $k$-algebra map compatible with comultiplication and counit) which is injective as a function. Then for every $c \in C$ with $\varepsilon_C(c) = 0$ such that $\iota(c)$ lies in the square of the augmentation ideal $\ker(\varepsilon_D) \subseteq D$, the element $c$ lies in the square of the augmentation ideal $\ker(\varepsilon_C) \subseteq C$; here the augmentation ideals are taken as the kernels of the counits viewed as $k$-algebra homomorphisms. Note that $C$ is not assumed to be finite over $k$, nor to carry an antipode.
--
--   In geometric terms, for a finite group scheme $G = \operatorname{Spec} D$ of height at most one over $k$ and a quotient $Q = \operatorname{Spec} C$ of it, the statement says that $\ker(\varepsilon_C) \cap \iota^{-1}(\ker(\varepsilon_D)^2) = \ker(\varepsilon_C)^2$, i.e. the map of cotangent spaces at the identity $\omega_Q \to \omega_G$ is injective, equivalently that $\operatorname{Lie}(G) \to \operatorname{Lie}(Q)$ is surjective. It is used in the construction of primitive elements lifting a given element along a surjection of height-one Hopf algebras.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_mem_ker_counit_sq_of_map_mem_sq_of_injective_of_forall_pow_prime_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

theorem HopfAlgebra.mem_ker_counit_sq_of_map_mem_sq_of_injective_of_forall_pow_prime_eq_zero
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (D : Type v) [CommRing D] [HopfAlgebra k D] [Module.Finite k D]
    (hD : ∀ x : D, Coalgebra.counit (R := k) x = 0 → x ^ p = 0)
    (C : Type w) [CommRing C] [Bialgebra k C]
    (ι : C →ₐc[k] D) (hι : Function.Injective ι)
    (c : C) (hc : Coalgebra.counit (R := k) c = 0)
    (h : ι c ∈ RingHom.ker (Bialgebra.counitAlgHom k D) ^ 2) :
    c ∈ RingHom.ker (Bialgebra.counitAlgHom k C) ^ 2 := by sorry
