-- Prove2me | Theorems.Thm_FractionalIdeal_finprod_unitOfPrime_zpow_count
-- name    : FractionalIdeal.finprod_unitOfPrime_zpow_count
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:31:38.911347+00:00
-- url     : https://prove2.me/theorems/fb121d64-095a-4ed7-88f6-89cb19c254a8
-- title:
--   Prime-power factorization of an invertible fractional ideal
-- statement:
--   Let $R$ be a Dedekind domain with fraction field $K$, and let $I$ be an invertible fractional ideal of $R$. For each nonzero prime $\mathfrak p$, let $v_{\mathfrak p}(I)\in\mathbb Z$ be its exponent in $I$. In the group of invertible fractional ideals,
--
--   $$
--   I=\prod_{\mathfrak p}\mathfrak p^{v_{\mathfrak p}(I)}.
--   $$
--
--   Only finitely many exponents are nonzero.
--
--   This states unique ideal factorization directly in the multiplicative group of invertible fractional ideals.
--
--   Source: the [Tau Ceti contributors](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/RingTheory/DedekindDomain/Factorization.lean#L152-L169) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`).
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/RingTheory/DedekindDomain/Factorization.lean#L152-L169

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_Factorization
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Complements on Dedekind-domain factorization

Facts about `Associates.count` and `FractionalIdeal.count` that Mathlib does not carry, together
with unit-level factorization of invertible fractional ideals.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.le_count_associates_iff_le_pow`: the multiplicity of `v` in
  a nonzero `J` is at least `k` exactly when `v ^ k` contains `J`. The multiplicity here is
  `Associates.count`, not `FractionalIdeal.count` — hence the `associates` token, matching
  Mathlib's `Ideal.count_associates_factors_eq` for the same expression. Mathlib reads that
  multiplicity as divisibility of `Associates`; a consumer comparing two multiplicities across a
  ring extension wants a containment of *ideals*, and shows the two ideals contain the same prime
  powers.
* `FractionalIdeal.count_div`: the multiplicity of `I / J` is the difference of the multiplicities
  of `I` and `J`. Mathlib's `count` API has `count_mul`, `count_inv`, `count_pow` and `count_zpow`
  but no division form, so every consumer that clears a denominator repeats the same rewrites.
* `FractionalIdeal.count_spanSingleton_div`: the same on principal fractional ideals. This is the
  one the `S`-integer class-group computation in
  `TauCeti/RingTheory/DedekindDomain/SInteger/ClassGroup.lean` uses, at both `R` and `𝒪_S` — which
  is why the ring is a variable rather than fixed — advancing
  `TauCetiRoadmap/EllipticCurves/README.md` §Layer 6 (Mordell–Weil), whose weak-Mordell–Weil
  argument needs the `S`-class group to be finite. It is also the step that carries
  `count_toPrincipalIdeal_eq_neg_log_valuation` below. `count_div` is its general form and has no
  consumer in this repository yet.
* `FractionalIdeal.count_toPrincipalIdeal_eq_neg_log_valuation`: the multiplicity at `v` of the
  principal fractional ideal of a nonzero rational function `u : Kˣ` is
  `-WithZero.log (v.valuation K u)`. This is the passage between the two ways this library measures
  a principal ideal at a height one prime — Mathlib's `count` and the adic valuation.
* `Ideal.hasFiniteMulSupport_asIdeal_pow_of_le_count`: a family of prime powers whose exponents
  are bounded by the multiplicities of a fixed nonzero ideal has finite multiplicative support.
  Mathlib's `Ideal.hasFiniteMulSupport` is the case of the multiplicities themselves; a consumer
  defining an ideal as `∏ᵥ 𝔭ᵥ ^ e v` for exponents it only knows to be dominated by an actual
  factorisation — as the minimal discriminant ideal of an elliptic curve is dominated by the
  discriminant of any integral model — needs the bounded form to see that the product is finite.
* `IsDedekindDomain.HeightOneSpectrum.unitOfPrime`: a height-one prime regarded as an invertible
  fractional ideal.
* `FractionalIdeal.hasFiniteMulSupport_zpow_count`: a family of powers indexed by the height one
  primes, with the multiplicities of a fixed fractional ideal as exponents, has finite
  multiplicative support. The bases are an arbitrary family in an arbitrary `DivInvMonoid`, since
  nothing but the vanishing of almost all exponents is at stake; the unit-level factorization below
  is the case of the primes themselves.
* `FractionalIdeal.finprod_unitOfPrime_zpow_count`: unique factorization of an invertible
  fractional ideal, transported along `Units.coeHom`.

All these declarations are general facts about an arbitrary Dedekind domain, mentioning no
particular ring extension.

`le_count_associates_iff_le_pow` is adapted from Michael Stoll's elliptic-curves formalisation
(`github.com/MichaelStollBayreuth/EllipticCurves`, `EllipticCurves/Mathlib/Basic.lean:381` at the
roadmap's pin `66889eada51a`, Apache 2.0, by Michael Stoll); following this repository's convention
for adapted material, the upstream authorship is credited here rather than in the copyright header.
**`count_div` and `count_spanSingleton_div` are new here** — they have no counterpart in that
source. `count_toPrincipalIdeal_eq_neg_log_valuation` is this repository's own, relocated here
from `TauCeti/AlgebraicGeometry/WeilDivisor/Dedekind/Basic.lean`: nothing in its statement or
proof mentions a Weil divisor, and stating it under `TauCeti.AlgebraicGeometry` put it out of
reach of the `RingTheory` consumers that need it, which is exactly the boundary
`TauCeti/RingTheory/ClassGroup/HeightOneSpectrum.lean` records in its module docstring.

The unit-level prime factorization `FractionalIdeal.finprod_unitOfPrime_zpow_count` is adapted
from Michael Stoll's `EllipticCurves/Mathlib/FractionalIdeal.lean` at commit `66889eada51a` of the
`MichaelStollBayreuth/EllipticCurves` repository (Apache 2.0).
-/
 section

namespace IsDedekindDomain.HeightOneSpectrum
end IsDedekindDomain.HeightOneSpectrum
section IsDedekindDomain.HeightOneSpectrum
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

open scoped nonZeroDivisors

variable {R : Type*} [CommRing R] [IsDedekindDomain R]







end IsDedekindDomain.HeightOneSpectrum

namespace Ideal
end Ideal
section Ideal
open Ideal

-- `Ideal.IsDedekindDomain` also exists, so the root namespace has to be named explicitly.
open _root_.IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R]



end Ideal

namespace FractionalIdeal
end FractionalIdeal
section FractionalIdeal
open FractionalIdeal

open IsDedekindDomain

open scoped nonZeroDivisors

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

theorem FractionalIdeal.finprod_unitOfPrime_zpow_count (I : (_root_.FractionalIdeal R⁰ K)ˣ) :
    I = ∏ᶠ v : _root_.IsDedekindDomain.HeightOneSpectrum R,
      v.unitOfPrime K ^ _root_.FractionalIdeal.count K v (I : _root_.FractionalIdeal R⁰ K) := by sorry
