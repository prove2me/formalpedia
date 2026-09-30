-- Prove2me | Theorems.Thm_Nat_prod_pow_factorization_sub_factorization_add_one_dvd
-- name    : Nat.prod_pow_factorization_sub_factorization_add_one_dvd
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:31:59.445089+00:00
-- url     : https://prove2.me/theorems/75f5ce57-e7fb-45f0-949d-a722ef5472d8
-- title:
--   Prime-power obstructions form a divisor
-- statement:
--   Let $f,h\in\mathbb N$ with $f\mid h$. Write $P(f)$ for the finite set of prime factors of $f$, with $P(0)=\varnothing$, and set $v_p(0)=0$. Then
--
--   $$
--   \prod_{p\in P(f)}p^{\max\{v_p(h)-v_p(f),0\}+1}\mid h.
--   $$
--
--   The tested prime-power obstructions combine into a single divisor, including the zero boundary case.
--
--   Source and proof credit: the Tau Ceti contributors, [original declaration and proof](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/Data/Nat/Factorization/MulDvd.lean#L100-L116), Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`; adapted to Lean 4.33.1.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/Data/Nat/Factorization/MulDvd.lean#L100-L116

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Nat.Factorization.Basic

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The prime powers that decide whether a divisor fits beside a fixed factor

Let `f` and `d` both divide `h`. Whether the product `f * d` still divides `h` is decided one
prime at a time, and only at the primes of `f`: room for `f * d` fails at `p` exactly when `d`
carries `p` to a power that exceeds the room `h` leaves after `f`, which is `v_p h - v_p f`. So
`f * d ∣ h` holds exactly when no prime `p` of `f` divides `d` to the exponent
`v_p h - v_p f + 1`.

The one-sided reading is what makes the statement useful: the primes outside `f` impose no
condition, because `d ∣ h` already leaves them enough room.

The exponents `v_p h - v_p f + 1` are themselves exponents of prime powers dividing `h`, both
one prime at a time and all at once, since the primes of `f` are distinct.

## Main results

* `Nat.mul_dvd_iff_forall_not_pow_dvd`: `f * d ∣ h` as non-divisibility of `d` by a
  prime power at each prime of `f`.
* `Nat.pow_factorization_sub_factorization_add_one_dvd`: the tested prime power divides `h`.
* `Nat.prod_pow_factorization_sub_factorization_add_one_dvd`: so does their product over the
  primes of `f`.
-/

 section

namespace Nat
end Nat
section Nat
open Nat

open Finset

theorem Nat.prod_pow_factorization_sub_factorization_add_one_dvd {f h : ℕ} (hf : f ∣ h) :
    (∏ p ∈ f.primeFactors, p ^ (h.factorization p - f.factorization p + 1)) ∣ h := by sorry
