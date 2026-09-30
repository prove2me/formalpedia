-- Prove2me | Theorems.Thm_Ideal_frobenius_fiber_eq_orbit_centralizer
-- name    : Ideal.frobenius_fiber_eq_orbit_centralizer
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:31:58.612913+00:00
-- url     : https://prove2.me/theorems/6b37bb88-c535-43f5-8701-2d71f0aa1daf
-- title:
--   A Frobenius fiber is a centralizer orbit
-- statement:
--   Let $L/K$ be a finite Galois extension of number fields with group $G$. Let $Q$ be a prime of $L$ over a prime $\mathfrak p$ of $K$, unramified over $K$, and let $\sigma\in G$ be its arithmetic Frobenius. Then
--
--   $$
--   \{P\mid\mathfrak p:\sigma\text{ is an arithmetic Frobenius at }P\}
--   =\{\tau(Q):\tau\in C_G(\sigma)\},
--   $$
--
--   where $P$ ranges over nonzero prime ideals of $\mathcal O_L$ and $C_G(\sigma)=\{\tau\in G:\tau\sigma=\sigma\tau\}$.
--
--   This describes the primes with a specified Frobenius element through the centralizer action.
--
--   Source: the [Tau Ceti contributors](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/Frobenius/FiberCount.lean#L65-L94) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`).
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/Frobenius/FiberCount.lean#L65-L94

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_NumberField_AutomorphismAction
import Definitions.Def_TauCeti_NumberTheory_NumberField_Frobenius_FiberCount
import Mathlib.Algebra.CharP.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Unramified.Locus

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# How many primes carry a given Frobenius element

Let `L / K` be a finite Galois extension of number fields, `𝔭` an ideal of `𝓞 K` and `σ` an
element of `Gal(L/K)`. The primes of `𝓞 L` above `𝔭` at which `σ` is an arithmetic Frobenius form
the *fiber* of `σ`, and `Ideal.frobenius_fiber_card_eq_of_isConj` shows that conjugate elements
have fibers of the same size. This file computes that size, at a prime where `σ` is a Frobenius
and `L / K` is unramified:

```text
#(fiber of σ) * orderOf σ = #Centralizer_{Gal(L/K)}(σ)
```

The reason is that the fiber is a single orbit. `Gal(L/K)` acts transitively on the primes above
`𝔭`, and the Frobenius at `τ • Q` is `τ σ τ⁻¹`, so the elements carrying `Q` to another member of
the fiber are exactly those commuting with `σ`. The stabilizer of `Q` inside that centralizer is
the decomposition group `⟨σ⟩`, whose order is `orderOf σ`, and the orbit-stabilizer theorem gives
the count.

The identity is stated as a product rather than as `#Centralizer(σ) / orderOf σ` so that it says
something without a separate divisibility: `orderOf σ` divides the centralizer's order because
`⟨σ⟩` is a subgroup of it, and `ConjClasses.card_carrier_mul_orderOf_dvd` records the companion
divisibility for a whole conjugacy class.

## Main results

* `Ideal.frobenius_fiber_eq_orbit_centralizer`: the fiber of `σ` above `𝔭` is the orbit of any of
  its members under the centralizer of `σ`.
* `Ideal.frobenius_fiber_card_mul_orderOf_eq_card_centralizer`: its size, times `orderOf σ`, is
  the order of that centralizer.
* `HeightOneSpectrum.frobeniusFiberEquiv`: the height-one-prime and ideal representations of the
  fiber are equivalent.

## References

* Sharifi, *Algebraic Number Theory*, Theorem 7.2.2 (p. 143).
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter I, §9.
-/

 section

open scoped NumberField Pointwise
open IsDedekindDomain (HeightOneSpectrum)

namespace Ideal
end Ideal
section Ideal
open Ideal

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L]

-- Source. The count is specified by the Chebotarev roadmap:
-- `TauCetiRoadmap/Chebotarev/README.md` §8.2, which displays the fibre size as
-- `#G / (#C * f) = #Centralizer_G(σ) / f` with `f = orderOf σ`. The theorems below count the
-- primes of `𝓞 L`; the roadmap's own statement counts primes of the fixed field `L ^ ⟨σ⟩`, and
-- reaches this one through the residue degree of a fixed-field prime.

theorem Ideal.frobenius_fiber_eq_orbit_centralizer (𝔭 : _root_.Ideal (𝓞 K)) {σ : L ≃ₐ[K] L}
    (Q : _root_.Ideal (𝓞 L)) [_root_.IsGalois K L] [Q.IsPrime] [Q.LiesOver 𝔭]
    [_root_.Algebra.IsUnramifiedAt (𝓞 K) Q]
    (hσ : _root_.IsArithFrobAt (𝓞 K) σ Q) :
    {P : _root_.Ideal (𝓞 L) | ∃ (_ : P.IsPrime) (_ : P.LiesOver 𝔭) (_ : P ≠ ⊥),
        _root_.IsArithFrobAt (𝓞 K) σ P}
      = _root_.MulAction.orbit (_root_.Subgroup.centralizer {σ}) Q := by sorry
