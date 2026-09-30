-- Prove2me | Theorems.Thm_NumberField_exists_auxiliaryPrime
-- name    : NumberField.exists_auxiliaryPrime
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:08:26.524383+00:00
-- url     : https://prove2.me/theorems/43f9b4de-7c11-4a0e-8f82-3b5a76cf8a0f
-- title:
--   The auxiliary prime
-- statement:
--   Let $K,L$ be number fields, let $n\ge1$ be a natural number, and let $N\in\mathbb N$ be a bound. There is a rational prime $q$ such that
--
--   $$
--   \begin{gathered}q>N,\qquad q\equiv1\pmod n,\qquad n\mid q-1,\\q\text{ is unramified in both }K\text{ and }L,\\\Phi_q(X)\text{ is irreducible over }K.\end{gathered}
--   $$
--
--   This supplies an auxiliary cyclotomic level with prescribed congruence and ramification properties; no inclusion between $K$ and $L$ is required.
--
--   Source and proof credit: the Tau Ceti contributors, [original declaration and proof](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/Chebotarev/AuxiliaryPrime.lean#L38-L68), Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`; adapted to Lean 4.33.1.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/Chebotarev/AuxiliaryPrime.lean#L38-L68

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.ExistsRamified
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Mathlib.RingTheory.RamificationInertia.Basic

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The auxiliary prime

The Chebotarev density argument repeatedly needs a rational prime that is simultaneously large,
congruent to `1` modulo a prescribed level, unramified in two number fields, and such that the
cyclotomic polynomial stays irreducible over the base. This file produces one, with all of those
conditions as conclusions rather than as obligations left to the caller.

## Main results

* `NumberField.exists_auxiliaryPrime`

## Implementation notes

The conditions are conclusions rather than obligations on the caller because they are needed
together: a caller holding only the congruence would have to re-derive the bound against the
ramified primes of both fields before it could discharge the rest.
-/

 section

open Polynomial
open scoped NumberField

namespace NumberField
end NumberField
section NumberField
open NumberField

theorem NumberField.exists_auxiliaryPrime (K L : Type*) [_root_.Field K] [_root_.NumberField K] [_root_.Field L] [_root_.NumberField L]
    (n N : ℕ) (hn : n ≠ 0) :
    ∃ q : ℕ, q.Prime ∧ N < q ∧ q ≡ 1 [MOD n] ∧ n ∣ q - 1 ∧
      _root_.Algebra.IsUnramifiedIn (𝓞 K) (_root_.Ideal.span {(q : ℤ)}) ∧
      _root_.Algebra.IsUnramifiedIn (𝓞 L) (_root_.Ideal.span {(q : ℤ)}) ∧
      _root_.Irreducible (_root_.Polynomial.cyclotomic q K) := by sorry
