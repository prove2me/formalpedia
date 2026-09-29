-- Prove2me | Theorems.Thm_NumberField_InfPlaceDecomp_eq_one_of_mem_decomp_of_sq_eq_neg_one
-- name    : NumberField.InfPlaceDecomp.eq_one_of_mem_decomp_of_sq_eq_neg_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/ab6e7a8f-209a-534d-93af-b927208a4748
-- title:
--   Trivial archimedean decomposition groups when √-1∈ E
-- statement:
--   Let $E$ and $K$ be number fields with $K$ an $E$-algebra and $K/E$ Galois, and suppose there is an element $i \in E$ with $i^2 = -1$. Let $v$ be an infinite place of $K$ and let $g$ be an $E$-algebra automorphism of $K$ lying in [`NumberField.InfPlaceDecomp.decomp E K v`](def/NumberField_ArchimedeanIdeleModule.html#L23), that is, in the stabiliser of $v$ for the natural action of the group $K \simeq_{\mathrm{alg}[E]} K$ of $E$-automorphisms of $K$ on the infinite places of $K$. The conclusion is that $g$ is the identity automorphism. Equivalently, under the hypothesis that $E$ contains a square root of $-1$, the archimedean decomposition group of every infinite place of $K$ over $E$ is trivial; the statement is phrased elementwise rather than as an equality of subgroups.
--
--   This is the archimedean unramifiedness statement: a number field containing $\sqrt{-1}$ has no real places, so no infinite place of a Galois extension $K/E$ ramifies and all archimedean decomposition groups are trivial. It is used in the local-invariant computations [`NumberField.LevelArith.finsum_apply_eq_zero_of_isBrauerLocalInv`](thm.html#NumberField.LevelArith.finsum_apply_eq_zero_of_isBrauerLocalInv) and [`NumberField.LevelArith.injective_of_isBrauerLocalInv`](thm.html#NumberField.LevelArith.injective_of_isBrauerLocalInv), where the infinite places must be discarded.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_InfPlaceDecomp_eq_one_of_mem_decomp_of_sq_eq_neg_one.lean

import Mathlib
import Definitions.Def_NumberField_ArchimedeanIdeleModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open NumberField
open scoped NumberField.InfPlaceDecomp

theorem NumberField.InfPlaceDecomp.eq_one_of_mem_decomp_of_sq_eq_neg_one
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (i : E) (hi : i ^ 2 = -1)
    (v : InfinitePlace K) (g : K ≃ₐ[E] K) (hg : g ∈ NumberField.InfPlaceDecomp.decomp E K v) : g = 1 := by sorry
