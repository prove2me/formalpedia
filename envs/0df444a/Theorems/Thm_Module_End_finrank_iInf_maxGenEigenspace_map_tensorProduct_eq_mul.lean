-- Prove2me | Theorems.Thm_Module_End_finrank_iInf_maxGenEigenspace_map_tensorProduct_eq_mul
-- name    : Module.End.finrank_iInf_maxGenEigenspace_map_tensorProduct_eq_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/3c1b61f1-56fe-59f4-b76d-60f74e5ed05d
-- title:
--   Dimension of simultaneous generalised eigenspaces on a tensor product
-- statement:
--   Let $F$ be a field, and let $V$ and $W$ be finite-dimensional $F$-vector spaces. Let $\iota$ and $\kappa$ be arbitrary types (no finiteness or nonemptiness assumed), let $A : \iota \to \operatorname{End}_F(V)$ and $B : \kappa \to \operatorname{End}_F(W)$ be families of $F$-linear endomorphisms, with no commutativity hypotheses, and let $\mu : \iota \to F$ and $\nu : \kappa \to F$ be families of scalars. For an endomorphism $f$ and a scalar $\lambda$, `Module.End.maxGenEigenspace f λ` denotes the maximal generalised eigenspace, the union over $k$ of $\ker (f - \lambda)^k$. Inside $V \otimes_F W$ form the submodule obtained by intersecting the generalised eigenspaces of the operators $A_i \otimes \mathrm{id}_W$ for the scalars $\mu_i$, over all $i \in \iota$, with the generalised eigenspaces of the operators $\mathrm{id}_V \otimes B_j$ for the scalars $\nu_j$, over all $j \in \kappa$. The assertion is that the $F$-dimension of this submodule equals the product of the $F$-dimension of $\bigcap_{i} \ker^{\infty}(A_i - \mu_i) \subseteq V$ with the $F$-dimension of $\bigcap_{j} \ker^{\infty}(B_j - \nu_j) \subseteq W$. With $\iota$ and $\kappa$ empty this specialises to $\dim_F (V \otimes_F W) = \dim_F V \cdot \dim_F W$.
--
--   This is the multiplicativity of simultaneous generalised eigenspace dimensions under tensor product, for two commuting families of operators each acting through one factor. It is used to compute the dimension of the part of an old space with prescribed generalised $U_q$-eigenvalues, the old space being a tensor product over the primes $q$ of the level of local $U_q$-strings; the result is cited by [`Module.End.finrank_iInf_maxGenEigenspace_eq_prod_rootMultiplicity_of_apply_eq_sum_update`](thm.html#Module.End.finrank_iInf_maxGenEigenspace_eq_prod_rootMultiplicity_of_apply_eq_sum_update).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_End_finrank_iInf_maxGenEigenspace_map_tensorProduct_eq_mul.lean

import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.TensorProduct.Finite

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem Module.End.finrank_iInf_maxGenEigenspace_map_tensorProduct_eq_mul
    (F : Type) [Field F]
    (V W : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    {ι κ : Type} (A : ι → Module.End F V) (μ : ι → F) (B : κ → Module.End F W) (ν : κ → F) :
    Module.finrank F
      ↥((⨅ i : ι, Module.End.maxGenEigenspace (TensorProduct.map (A i) (LinearMap.id : W →ₗ[F] W)) (μ i)) ⊓
        (⨅ j : κ, Module.End.maxGenEigenspace (TensorProduct.map (LinearMap.id : V →ₗ[F] V) (B j)) (ν j))) =
    Module.finrank F ↥(⨅ i : ι, Module.End.maxGenEigenspace (A i) (μ i)) *
      Module.finrank F ↥(⨅ j : κ, Module.End.maxGenEigenspace (B j) (ν j)) := by sorry
