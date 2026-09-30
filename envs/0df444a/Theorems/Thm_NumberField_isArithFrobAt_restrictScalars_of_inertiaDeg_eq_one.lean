-- Prove2me | Theorems.Thm_NumberField_isArithFrobAt_restrictScalars_of_inertiaDeg_eq_one
-- name    : NumberField.isArithFrobAt_restrictScalars_of_inertiaDeg_eq_one
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:45:01.335786+00:00
-- url     : https://prove2.me/theorems/51852e05-0827-44d9-a15e-8355181d106d
-- title:
--   Restriction of a relative Frobenius at residue degree one
-- statement:
--   Let $K\subseteq M\subseteq L$ be a tower of number fields and let $Q$ be a prime of $\mathcal O_L$. Put $P=Q\cap\mathcal O_M$ and $\mathfrak p=Q\cap\mathcal O_K$. If $\tau\in\operatorname{Aut}_M(L)$ is an arithmetic Frobenius at $Q$ over $M$ and $f(P/\mathfrak p)=1$, then
--
--   $$
--   \tau\text{, regarded as a }K\text{-automorphism, is an arithmetic Frobenius at }Q\text{ over }K.
--   $$
--
--   Neither Galoisness of $L/K$ nor unramifiedness of $Q$ is assumed.
--
--   This provides the local compatibility of Frobenius conditions needed at degree-one primes.
--
--   Source: the [Tau Ceti contributors](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/Frobenius/Tower.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`).
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/Frobenius/Tower.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_NumberField_AutomorphismAction
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
# Raising the base field: the tower formula for arithmetic Frobenius elements

Let `K ⊆ M ⊆ L` be number fields with `L / K` and `L / M` Galois, let `Q` be a prime of `𝓞 L`
unramified over `𝓞 K`, and write `𝔓 = Q ∩ 𝓞 M` and `𝔭 = Q ∩ 𝓞 K`. An arithmetic Frobenius
`σ ∈ Gal(L/K)` at `Q` acts on the residue field by `x ↦ x ^ 𝔑𝔭`, while an arithmetic Frobenius
`τ ∈ Gal(L/M)` at `Q` acts by `x ↦ x ^ 𝔑𝔓`. Since `𝔑𝔓 = 𝔑𝔭 ^ f(𝔓/𝔭)`, the two are related by

```text
AlgEquiv.restrictScalars K τ = σ ^ f(𝔓/𝔭).
```

The exponent is a **power**, the residue degree of the intermediate prime over the base, and never
an inverse. In particular `σ ^ f(𝔓/𝔭)` fixes `M` pointwise even though `M / K` need not be normal
and `σ` itself need not preserve `M`.

This is the second of the two tower laws for Frobenius elements. The first, restriction along a
normal subextension, takes no power at all and is
`IsArithFrobAt.restrictNormal` in `TauCeti.NumberTheory.NumberField.Frobenius.Restriction`.

## The two hypotheses that are not decoration

The statement is *relative to one prime `Q` of `L`*. Replacing `σ` by an arbitrary conjugate — an
arbitrary representative of the Artin class of `𝔭` — makes it false when `M / K` is not normal: a
conjugate need not stabilize `Q`, so its `f`-th power need not fix `M` pointwise, and it is then
the restriction of no element of `Gal(L/M)` at all.

Unramifiedness of `Q` over `𝓞 K` is likewise essential. At a ramified prime a Frobenius lift is
determined only modulo inertia, so there is no equality of automorphisms to prove; the statement
would have to be made in the quotient by the inertia subgroup, or about a coset. Here
unramifiedness enters through `Ideal.stabilizerHom_injective_of_isUnramifiedAt`: the decomposition
group of `Q` embeds into the automorphism group of the residue extension, so an element of
`Gal(L/K)` stabilizing `Q` is pinned down by its residue action, and both `σ ^ f(𝔓/𝔭)` and
`AlgEquiv.restrictScalars K τ` act by `x ↦ x ^ 𝔑𝔓`.

## Main results

* `NumberField.restrictScalars_eq_pow_inertiaDeg`: an arithmetic Frobenius of `Gal(L/M)` at `Q`
  restricts to the `f(𝔓/𝔭)`-th power of an arithmetic Frobenius of `Gal(L/K)` at `Q`.
* `NumberField.isArithFrobAt_iff_restrictScalars_eq_pow_inertiaDeg`: that power characterizes the
  relative Frobenius among the elements of `Gal(L/M)` after restriction to `Gal(L/K)`.
* `NumberField.restrictScalars_arithFrobAt_eq_pow_inertiaDeg`: the same formula for Mathlib's
  coherently chosen `arithFrobAt`, which is what the Artin symbol is built from.
* `NumberField.exists_isArithFrobAt_pow_inertiaDeg`: the existence form of the tower formula,
  stated for prime ideals `𝔓` and `𝔭` presented by their defining equations.
* `NumberField.pow_inertiaDeg_apply_algebraMap`: the `f(𝔓/𝔭)`-th power of `σ` fixes `M`
  pointwise.
* `NumberField.restrictScalars_eq_of_inertiaDeg_eq_one`: at residue degree one the restriction
  of the relative Frobenius is `σ` itself, with no power.
* `NumberField.isArithFrobAt_restrictScalars_of_inertiaDeg_eq_one`: the same at residue degree
  one, concluding that the restriction is an arithmetic Frobenius rather than assuming one.
* `NumberField.isArithFrobAt_int_of_absNorm_eq`: a relative Frobenius above an ideal of absolute
  norm `p` is also a Frobenius over the ideal `(p)` of `ℤ`.
* `NumberField.isArithFrobAt_one_of_pow_eq_one` and
  `NumberField.isArithFrobAt_eq_one_of_pow_eq_one`: when an absolute Frobenius at `Q` has order
  dividing `n` and the residue field of `Q ∩ 𝓞 M` has `p ^ n` elements, the relative Frobenius
  of `Gal(L/M)` at `Q` is the identity.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter I, §9.
-/

 section

open Ideal

open scoped NumberField Pointwise

namespace NumberField
end NumberField
section NumberField
open NumberField

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] {M : Type*} [Field M] [NumberField M] [Algebra K M] [Algebra M L]
  [IsScalarTower K M L] {Q : Ideal (𝓞 L)} [Q.IsPrime]















omit [_root_.IsGalois K L]

theorem NumberField.isArithFrobAt_restrictScalars_of_inertiaDeg_eq_one
    {τ : L ≃ₐ[M] L} (hτ : _root_.IsArithFrobAt (𝓞 M) τ Q)
    (hf : (Q.under (𝓞 M)).inertiaDeg (𝓞 K) = 1) :
    _root_.IsArithFrobAt (𝓞 K) (_root_.AlgEquiv.restrictScalars K τ) Q := by sorry
