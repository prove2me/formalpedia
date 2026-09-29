-- Prove2me | Theorems.Thm_Module_Flat_lTensor_injective_of_exact_of_surjective_of_flat
-- name    : Module.Flat.lTensor_injective_of_exact_of_surjective_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/eca63938-4a18-56e4-91da-bfdd08a2d953
-- title:
--   Left exactness after tensoring when the cokernel is flat
-- statement:
--   Let $R$ be a commutative ring and let $N$, $M$, $P$ be $R$-modules (all types in the same universe). Given $R$-linear maps $f\colon N \to M$ and $g\colon M \to P$ such that $f$ is injective, the pair $(f,g)$ is exact in the sense of `Function.Exact`, i.e. the range of $f$ coincides with the kernel of $g$ (pointwise: $g(m)=0$ if and only if $m$ lies in the image of $f$), and $g$ is surjective — so that $0 \to N \to M \to P \to 0$ is a short exact sequence — and assuming moreover that $P$ is a flat $R$-module, the conclusion is: for every $R$-module $A$, the map $\mathrm{id}_A \otimes f =$ `f.lTensor A` $\colon A \otimes_R N \to A \otimes_R M$ is injective. Only injectivity of the left-hand map is asserted; the surjectivity of $A \otimes_R M \to A \otimes_R P$ and the exactness in the middle of the tensored sequence are not part of the statement.
--
--   This is the standard fact that a short exact sequence with flat cokernel is universally exact on the left, equivalently that $\mathrm{Tor}_1^R(A,P)=0$ for flat $P$; it is phrased without Tor functors, purely in terms of injectivity after tensoring. It is used in the project by [`Ideal.exists_notMem_and_forall_mul_eq_zero_of_flat_quotient_of_rTensor_injective`](thm.html#Ideal.exists_notMem_and_forall_mul_eq_zero_of_flat_quotient_of_rTensor_injective), [`Module.Flat.ker_baseChange_eq_bot_and_ker_le_range_of_flat_of_exact`](thm.html#Module.Flat.ker_baseChange_eq_bot_and_ker_le_range_of_flat_of_exact) and [`Module.Flat.ker_of_surjective_of_flat`](thm.html#Module.Flat.ker_of_surjective_of_flat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_Flat_lTensor_injective_of_exact_of_surjective_of_flat.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open TensorProduct

theorem Module.Flat.lTensor_injective_of_exact_of_surjective_of_flat
    {R : Type u} [CommRing R] {N M P : Type u}
    [AddCommGroup N] [Module R N] [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    (f : N →ₗ[R] M) (g : M →ₗ[R] P) (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) [Module.Flat R P]
    (A : Type u) [AddCommGroup A] [Module R A] :
    Function.Injective (f.lTensor A) := by sorry
