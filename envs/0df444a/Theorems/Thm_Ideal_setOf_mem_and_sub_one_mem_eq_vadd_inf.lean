-- Prove2me | Theorems.Thm_Ideal_setOf_mem_and_sub_one_mem_eq_vadd_inf
-- name    : Ideal.setOf_mem_and_sub_one_mem_eq_vadd_inf
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:31:53.215476+00:00
-- url     : https://prove2.me/theorems/9237784d-bab9-4756-ae2f-742b3f0fcbc6
-- title:
--   An ideal congruence class is a coset of an intersection
-- statement:
--   Let $R$ be a ring and let $I,J$ be ideals of $R$. If $\xi\in I$ and $\xi-1\in J$, then
--
--   $$
--   \{x\in R:x\in I,\ x\equiv1\pmod J\}=\xi+(I\cap J).
--   $$
--
--   The ring need not be commutative.
--
--   This identifies simultaneous ideal membership and congruence conditions with one additive coset.
--
--   Source: the [Tau Ceti contributors](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/RingTheory/Ideal/CoprimeCoset.lean#L37-L55) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`).
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/RingTheory/Ideal/CoprimeCoset.lean#L37-L55

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.RingTheory.Ideal.Operations

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The elements of one ideal congruent to one modulo another

For ideals `I` and `J` of a commutative ring, the elements of `I` congruent to `1` modulo `J` form
a coset of `I ⊓ J` inside `I`, translated by any one of them.  Such an element exists exactly when
`I` and `J` are coprime, and coprimality also turns `I ⊓ J` into `I * J`.

This is the shape a counting argument wants: the set is a translate of a fixed subgroup, so it can
be enumerated by translating that subgroup once.

## Main results

* `Ideal.isCoprime_iff_exists_mem_and_sub_one_mem`: the set is nonempty exactly when `I`
  and `J` are coprime;
* `Ideal.setOf_mem_and_sub_one_mem_eq_vadd_inf`: the set is a coset of `I ⊓ J`;
* `Ideal.setOf_mem_and_sub_one_mem_eq_vadd_mul`: the same coset written over `I * J`.
-/

 section

namespace Ideal
end Ideal
section Ideal
open Ideal

section Ring

variable {R : Type*} [Ring R] {I J : Ideal R}

open Pointwise

theorem Ideal.setOf_mem_and_sub_one_mem_eq_vadd_inf {ξ : R} (hξI : ξ ∈ I) (hξJ : ξ - 1 ∈ J) :
    {x : R | x ∈ I ∧ x - 1 ∈ J} = ξ +ᵥ ((I ⊓ J : _root_.Ideal R) : _root_.Set R) := by sorry
