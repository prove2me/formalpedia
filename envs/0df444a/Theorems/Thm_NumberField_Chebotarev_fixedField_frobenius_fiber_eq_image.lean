-- Prove2me | Theorems.Thm_NumberField_Chebotarev_fixedField_frobenius_fiber_eq_image
-- name    : NumberField.Chebotarev.fixedField_frobenius_fiber_eq_image
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:07:12.179454+00:00
-- url     : https://prove2.me/theorems/95bd0fc6-a2bc-486e-b214-4252f1fd8aa5
-- title:
--   Contraction of a Frobenius fiber to a cyclic fixed field
-- statement:
--   Let $L/K$ be a finite Galois extension of number fields, $\sigma\in G=\operatorname{Gal}(L/K)$, and $E=L^{\langle\sigma\rangle}$. Let $\mathfrak p$ be an unramified prime of $K$ with arithmetic Frobenius class $[\sigma]$. Then
--
--   $$
--   \{\mathfrak P\mid\mathfrak p:\operatorname{Frob}_{\mathfrak P}(L/E)=\sigma\}
--   =\{\mathfrak Q\cap\mathcal O_E:\mathfrak Q\mid\mathfrak p,\ \operatorname{Frob}_{\mathfrak Q}(L/K)=\sigma\}.
--   $$
--
--   On the left, $\mathfrak P$ ranges over nonzero primes of $E$ unramified in $L$; on the right, $\mathfrak Q$ ranges over nonzero primes of $L$. The automorphism $\sigma$ on the left is regarded as an element of $\operatorname{Gal}(L/E)$.
--
--   This identifies the relative prime fiber used in fixed-field counting with the contraction of the absolute Frobenius fiber.
--
--   Source: the [Tau Ceti contributors](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/Chebotarev/FixedField/FiberCount.lean#L156-L195) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`).
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/Chebotarev/FixedField/FiberCount.lean#L156-L195

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_FieldTheory_Galois_FixedField
import Definitions.Def_TauCeti_NumberTheory_Chebotarev_FrobeniusPrimeSet
import Definitions.Def_TauCeti_NumberTheory_NumberField_ArtinSymbol
import Definitions.Def_TauCeti_NumberTheory_NumberField_AutomorphismAction
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.DedekindDomain.SelmerGroup
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.Tactic.Group

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Frobenius fibers over cyclic fixed fields

Let `L / K` be a finite Galois extension, let `C` be a conjugacy class in `Gal(L/K)`, and choose
`sigma` in `C`.  Put `E = L ^ <sigma>`.  This file counts the primes of `E` over a prime in the
Frobenius class `C` whose relative Frobenius in `L / E` is the automorphism induced by `sigma`:

```text
#G / (#C * orderOf sigma).
```

Contraction identifies these primes with the primes of `L` at which `sigma` itself is an
arithmetic Frobenius.  The latter form one orbit under the centralizer of `sigma`; its stabilizer
is `<sigma>`.  The resulting count is the fixed-field multiplicity used when transferring prime
sums and densities between `E` and `K`.

## Main result

* `NumberField.Chebotarev.fixedField_frobenius_fiber_eq_image`: contraction identifies the
  relative fiber with the image of the corresponding absolute Frobenius fiber.
* `NumberField.Chebotarev.inertiaDeg_eq_one_iff_under_mem_frobeniusPrimeSet`: away from the
  ramified primes, a prime of the relative fiber has residue degree one over `K` exactly when the
  prime below it lies in the Frobenius fiber of `sigma`.
* `NumberField.Chebotarev.fixedField_frobenius_fiber_card`: the exact cardinality of the relative
  Frobenius fiber over one prime of `K`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, Section 9.
* R. Sharifi, *Algebraic Number Theory*, Theorem 7.2.2.
* C. Birkbeck and R. Brasca,
  [*Chebotarev density*](https://github.com/CBirkbeck/chebotarev-density),
  `CebotarevDensity/FixedFieldDensity.lean` at commit
  `55a89985d47a3befcf6069aca1da250ff088b5c7` (Apache-2.0).
-/

 section

open IntermediateField
open scoped NumberField Pointwise
open IsDedekindDomain (HeightOneSpectrum)

namespace NumberField.Chebotarev
end NumberField.Chebotarev
section NumberField.Chebotarev
open NumberField NumberField.Chebotarev

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

theorem NumberField.Chebotarev.fixedField_frobenius_fiber_eq_image
    (sigma : L ≃ₐ[K] L) (p : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hp : p ∈ _root_.NumberField.Chebotarev.frobeniusPrimeSet K L (_root_.ConjClasses.mk sigma)) :
    {P : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 ↥(_root_.IntermediateField.fixedField (_root_.Subgroup.zpowers sigma))) |
        P.under (𝓞 K) = p ∧
          P ∈ _root_.NumberField.Chebotarev.frobeniusPrimeSet ↥(_root_.IntermediateField.fixedField (_root_.Subgroup.zpowers sigma)) L
            (_root_.ConjClasses.mk sigma.toFixedFieldAlgEquiv)} =
      (fun Q : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 L) ↦
        Q.under (𝓞 ↥(_root_.IntermediateField.fixedField (_root_.Subgroup.zpowers sigma)))) ''
        {Q : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 L) |
          Q.under (𝓞 K) = p ∧ _root_.IsArithFrobAt (𝓞 K) sigma Q.asIdeal} := by sorry
