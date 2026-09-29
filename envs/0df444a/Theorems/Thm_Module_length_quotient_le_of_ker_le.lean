-- Prove2me | Theorems.Thm_Module_length_quotient_le_of_ker_le
-- name    : Module.length_quotient_le_of_ker_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/15531aef-af67-5683-bc95-1c016bb5b637
-- title:
--   Length of M/K bounded by length of N when ker f ⊆ K
-- statement:
--   Let $R$ be a commutative ring and let $M$ and $N$ be $R$-modules (given as additive commutative groups with $R$-module structures, with the ambient types taken in the lowest universe). Given a submodule $K \le M$, an $R$-linear map $f : M \to N$, and the hypothesis that $\ker f \le K$ as submodules of $M$, the conclusion is the inequality $\ell_R(M/K) \le \ell_R(N)$ between the Mathlib module lengths, i.e. between the suprema of lengths of chains of submodules, taken in $\mathbb{N}\cup\{\infty\}$; here $M/K$ is the quotient module $M ⧸ K$. No finiteness hypothesis is imposed on either side: if $\ell_R(N)$ is infinite the statement is vacuous, and the inequality is asserted in the extended value range.
--
--   An elementary monotonicity statement for module length: a quotient by a submodule containing the kernel of a linear map has length at most that of the target. It is used by [`GaloisRep.DeformationRingData.length_level_quotient_le_of_ordinaryLine`](thm.html#GaloisRep.DeformationRingData.length_level_quotient_le_of_ordinaryLine) to bound the length of a level quotient through an explicit linear invariant rather than via an inclusion of submodules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_length_quotient_le_of_ker_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Module.length_quotient_le_of_ker_le
    {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (K : Submodule R M) (f : M →ₗ[R] N) (h : LinearMap.ker f ≤ K) :
    Module.length R (M ⧸ K) ≤ Module.length R N := by sorry
