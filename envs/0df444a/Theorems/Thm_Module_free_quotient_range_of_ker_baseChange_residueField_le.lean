-- Prove2me | Theorems.Thm_Module_free_quotient_range_of_ker_baseChange_residueField_le
-- name    : Module.free_quotient_range_of_ker_baseChange_residueField_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/b6dad48e-a9a3-5697-9c90-ba475b66d460
-- title:
--   Cokernel of a map to a finite free module is free when residual relations lift
-- statement:
--   Let $R$ be a commutative local ring with residue field $k =$ `IsLocalRing.ResidueField R`, and let $M$ and $N$ be $R$-modules, each module-finite over $R$, with $N$ free over $R$. Let $f : M \to N$ be $R$-linear. The hypothesis is an inclusion of submodules of $k \otimes_R M$: the kernel of the base-changed map $f \otimes_R k : k \otimes_R M \to k \otimes_R N$ is contained in the image of the map $k \otimes_R \ker f \to k \otimes_R M$ obtained by base-changing the inclusion $\ker f \hookrightarrow M$. In other words, every relation among the images of generators of $M$ in $N$ that holds after reduction modulo the maximal ideal comes from a relation holding over $R$. The conclusion is that the quotient $N / \operatorname{im} f$, i.e. the cokernel of $f$, is a free $R$-module.
--
--   Since $N$ is finite free, the hypothesis is the classical condition $\operatorname{Tor}_1^R(N/\operatorname{im} f, k) = 0$ for the finitely presented module $N/\operatorname{im} f$, and the statement is the standard criterion that such a module over a local ring is free. It is used in the construction of the Hilbert functor, via [`AlgebraicGeometry.HilbertFunctor.free_piece_of_isLocalRing_of_forall_relation_mem_span`](thm.html#AlgebraicGeometry.HilbertFunctor.free_piece_of_isLocalRing_of_forall_relation_mem_span), to produce free pieces over local rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_free_quotient_range_of_ker_baseChange_residueField_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

open scoped TensorProduct

theorem Module.free_quotient_range_of_ker_baseChange_residueField_le
    {R : Type u} [CommRing R] [IsLocalRing R]
    {M : Type v} {N : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N] [Module.Free R N] (f : M →ₗ[R] N)
    (h : LinearMap.ker (f.baseChange (IsLocalRing.ResidueField R)) ≤
      LinearMap.range ((LinearMap.ker f).subtype.baseChange (IsLocalRing.ResidueField R))) :
    Module.Free R (N ⧸ LinearMap.range f) := by sorry
