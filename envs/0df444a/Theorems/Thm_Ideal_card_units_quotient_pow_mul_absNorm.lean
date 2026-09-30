-- Prove2me | Theorems.Thm_Ideal_card_units_quotient_pow_mul_absNorm
-- name    : Ideal.card_units_quotient_pow_mul_absNorm
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:31:36.645729+00:00
-- url     : https://prove2.me/theorems/72df7885-faaf-4534-8655-a58b6da47aaa
-- title:
--   Counting units modulo a prime-power ideal
-- statement:
--   Let $R$ be an infinite Dedekind domain that is free as a $\mathbb Z$-module. Let $P$ be a maximal ideal, let $e\ge1$, and suppose $R/P^e$ is finite. Writing $NJ=|R/J|$ for the absolute norm of the ideals occurring below,
--
--   $$
--   |(R/P^e)^\times|\,NP=N(P^e)(NP-1).
--   $$
--
--   This is the prime-power Euler factor for the number of invertible residue classes.
--
--   Source: the [Tau Ceti contributors](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/RingTheory/DedekindDomain/Totient.lean#L43-L66) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`).
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/RingTheory/DedekindDomain/Totient.lean#L43-L66

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Euler's totient for ideals of a Dedekind domain

For an ideal `I` of an infinite Dedekind domain `R` whose quotient `R ⧸ I` is finite, this file
counts the units of `R ⧸ I` in terms of the absolute norm `N = Ideal.absNorm`:
`#(R ⧸ I)ˣ = N I · ∏_{𝔭 ∣ I} (1 - (N 𝔭)⁻¹)`, the product running over the height-one primes
dividing `I`. For `R = ℤ` this is Euler's product formula for the totient.

The set of primes dividing `I` is passed as a `Finset` `S` together with the characterisation
`∀ v, v ∈ S ↔ v.asIdeal ∣ I`, so that any concrete description of the prime divisors of `I` can
be used directly.

## Main results

* `Ideal.card_units_quotient_pow_mul_absNorm`: `#(R ⧸ P ^ e)ˣ · N P = N (P ^ e) · (N P - 1)` for a
  maximal ideal `P` and `e ≠ 0`.
* `Ideal.card_units_quotient_mul_prod_absNorm`: `#(R ⧸ I)ˣ · ∏_{𝔭 ∈ S} N 𝔭 = N I · ∏_{𝔭 ∈ S}
  (N 𝔭 - 1)` in `ℕ`, the analogue of `Nat.totient_mul_prod_primeFactors`.
* `Ideal.card_units_quotient_eq_absNorm_mul_prod`: `#(R ⧸ I)ˣ = N I · ∏_{𝔭 ∈ S} (1 - (N 𝔭)⁻¹)`
  in any field of characteristic zero, the analogue of `Nat.totient_eq_mul_prod_factors`.
-/

 section

open IsDedekindDomain

namespace Ideal
end Ideal
section Ideal
open Ideal

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Infinite R] [Module.Free ℤ R]

theorem Ideal.card_units_quotient_pow_mul_absNorm (P : _root_.Ideal R) [P.IsMaximal] {e : ℕ} (he : e ≠ 0)
    [_root_.Finite (R ⧸ P ^ e)] :
    _root_.Nat.card (R ⧸ P ^ e)ˣ * _root_.Ideal.absNorm P = _root_.Ideal.absNorm (P ^ e) * (_root_.Ideal.absNorm P - 1) := by sorry
