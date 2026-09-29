-- Prove2me | Theorems.Thm_IsSMulRegular_tensorProduct_of_flat_quotSMulTop
-- name    : IsSMulRegular.tensorProduct_of_flat_quotSMulTop
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/30504d35-fbe2-5641-8be5-3223705f5cb9
-- title:
--   Regularity of t on M ⊗_A B from flatness of B/tB
-- statement:
--   Let $A$ be a commutative ring and $t \in A$, and let $B$ and $M$ be $A$-modules. Assume that multiplication by $t$ is injective on $A$, on $B$ and on $M$ (`IsSMulRegular` for each), and assume that the $A/(t)$-module $B/tB$, written `QuotSMulTop t B` and defined as the quotient of $B$ by the submodule $t \cdot \top$, is flat over the quotient ring $A ⧸ \mathrm{span}\,\{t\}$. The conclusion is that multiplication by $t$ is injective on the tensor product $M \otimes_A B$, i.e. $t \cdot y = 0$ forces $y = 0$ there. No finiteness or Noetherian hypothesis is imposed on $A$, $B$ or $M$, and the three modules live in arbitrary universes.
--
--   This is the elementary ‘purity’ half of a fibrewise criterion of flatness over a principal ideal ring with no finiteness assumptions: regularity of $t$ on the factors plus flatness of the reduction $B/tB$ propagates regularity of $t$ to the tensor product. It is used in the proof of [`Module.Flat.of_forall_flat_residueField_tensorProduct_of_isPrincipalIdealRing`](thm.html#Module.Flat.of_forall_flat_residueField_tensorProduct_of_isPrincipalIdealRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsSMulRegular_tensorProduct_of_flat_quotSMulTop.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

universe u v w

theorem IsSMulRegular.tensorProduct_of_flat_quotSMulTop
    {A : Type u} [CommRing A] (t : A) {B : Type v} [AddCommGroup B] [Module A B]
    {M : Type w} [AddCommGroup M] [Module A M]
    (htA : IsSMulRegular A t) (htB : IsSMulRegular B t) (htM : IsSMulRegular M t)
    [Module.Flat (A ⧸ Ideal.span {t}) (QuotSMulTop t B)] :
    IsSMulRegular (M ⊗[A] B) t := by sorry
