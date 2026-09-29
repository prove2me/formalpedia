-- Prove2me | Theorems.Thm_HopfAlgebra_exists_fin_lift_basis_ker_counitAlgHom_sq_of_finiteType
-- name    : HopfAlgebra.exists_fin_lift_basis_ker_counitAlgHom_sq_of_finiteType
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/cef9eeda-00e1-575e-9f34-1786771283e4
-- title:
--   Finite basis of I/I² at the augmentation ideal
-- statement:
--   Let $K$ be a field and let $A$ be a commutative ring carrying a Hopf algebra structure over $K$ which is of finite type as a $K$-algebra. Write $I = \ker\varepsilon$ for the kernel of the ring homomorphism underlying the counit algebra map `Bialgebra.counitAlgHom K A` $\colon A \to K$. The assertion is that there exist a natural number $n$ and a family $\xi \colon \mathrm{Fin}\,n \to A$ with the following three properties: (i) each $\xi_i$ lies in $I$; (ii) the family of images of the $\xi_i$ under the quotient map $A \to A/I^2$ is linearly independent over $K$ (linear independence is stated in the quotient ring $A/I^2$ viewed as a $K$-module, not in the submodule $I/I^2$); and (iii) for every $a \in I$ there are scalars $c_i \in K$ with $a - \sum_{i} c_i \xi_i \in I^2$. Thus the images of $\xi_1,\dots,\xi_n$ form a $K$-basis of $I/I^2$, in particular this cotangent space at the augmentation is finite-dimensional.
--
--   This is the finiteness statement about the cotangent space at the identity of an affine group scheme of finite type over a field, the input to Cartier's theorem that such a group scheme is smooth in characteristic zero. It is used by [`HopfAlgebra.isDomain_localization_atPrime_ker_counitAlgHom_of_finiteType_of_charZero`](thm.html#HopfAlgebra.isDomain_localization_atPrime_ker_counitAlgHom_of_finiteType_of_charZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_fin_lift_basis_ker_counitAlgHom_sq_of_finiteType.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HopfAlgebra.exists_fin_lift_basis_ker_counitAlgHom_sq_of_finiteType
    (K : Type*) [Field K]
    (A : Type*) [CommRing A] [HopfAlgebra K A] [Algebra.FiniteType K A] :
    ∃ (n : ℕ) (ξ : Fin n → A),
      (∀ i, ξ i ∈ RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ∧
      LinearIndependent K
        (fun i ↦ Ideal.Quotient.mk ((RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ^ 2) (ξ i)) ∧
      (∀ a ∈ RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom,
        ∃ c : Fin n → K, a - ∑ i, c i • ξ i ∈ (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ^ 2) := by sorry
