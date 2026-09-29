-- Prove2me | Theorems.Thm_LinearMap_bijective_of_forall_bijective_baseChange_quotient_maximal
-- name    : LinearMap.bijective_of_forall_bijective_baseChange_quotient_maximal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/8b28a9e0-b548-55b5-b9db-6e8d8b0918f1
-- title:
--   Bijectivity from bijectivity of all residue base changes
-- statement:
--   Let $R$ be a commutative ring and let $M$ and $N$ be $R$-modules that are finite and free (carrying the usual additive group and module structures, with `Module.Finite` and `Module.Free` instances). Let $f \colon M \to N$ be an $R$-linear map, and suppose that for every ideal $\mathfrak m$ of $R$ that is maximal, the base change of $f$ along $R \to R/\mathfrak m$, that is the $R/\mathfrak m$-linear map $(R/\mathfrak m) \otimes_R M \to (R/\mathfrak m) \otimes_R N$ induced by $f$, is bijective as a function. The conclusion is that $f$ itself is bijective as a function, hence an isomorphism of $R$-modules. Note that no hypothesis of equal rank is imposed: the equality of the ranks of $M$ and $N$ is extracted from the hypothesis at a single maximal ideal, and the trivial ring is covered separately.
--
--   This is the standard fibrewise criterion for a map of finite free modules over a commutative ring to be an isomorphism: a determinant lies in every maximal ideal exactly when all residue fibres degenerate. It is used in the construction of Bezoutian-type pairings, namely by [`Algebra.bijective_rTensor_dual_bezoutian_of_forall_field`](thm.html#Algebra.bijective_rTensor_dual_bezoutian_of_forall_field), to descend a statement proved over fields to the base ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LinearMap_bijective_of_forall_bijective_baseChange_quotient_maximal.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem LinearMap.bijective_of_forall_bijective_baseChange_quotient_maximal
    {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Free R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Free R N] (f : M →ₗ[R] N)
    (h : ∀ (𝔪 : Ideal R) [𝔪.IsMaximal], Function.Bijective (f.baseChange (R ⧸ 𝔪))) :
    Function.Bijective f := by sorry
