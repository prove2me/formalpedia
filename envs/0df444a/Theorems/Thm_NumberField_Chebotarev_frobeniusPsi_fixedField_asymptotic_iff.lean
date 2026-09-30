-- Prove2me | Theorems.Thm_NumberField_Chebotarev_frobeniusPsi_fixedField_asymptotic_iff
-- name    : NumberField.Chebotarev.frobeniusPsi_fixedField_asymptotic_iff
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:14:45.547085+00:00
-- url     : https://prove2.me/theorems/cc8e1b9b-e554-49b0-86ab-b1e34ff359a6
-- title:
--   Transfer of Frobenius weighted asymptotics across a cyclic fixed field
-- statement:
--   Let $L/K$ be a finite Galois extension of number fields with group $G$, let $C$ be a conjugacy class, choose $\sigma\in C$, and put $E=L^{\langle\sigma\rangle}$ and $b=|G|/(|C|\operatorname{ord}(\sigma))$. This is a positive integer. For an extension $B/A$ and a conjugacy class $D$, write $\psi_{B/A,D}(x)$ for the sum of $\log N\mathfrak p$ over unramified prime powers $\mathfrak p^j$ with $j\ge1$, $N\mathfrak p^j\le x$, and $\operatorname{Frob}_{\mathfrak p}^{\,j}\in D$. For every $\delta\in\mathbb R$, as $x\to+\infty$,
--
--   $$
--   \psi_{L/E,[\sigma]}(x)=\delta x+o(x)
--   \quad\Longleftrightarrow\quad
--   \psi_{L/K,C}(x)=\frac\delta b x+o(x).
--   $$
--
--   This transfers weighted asymptotics between the cyclic extension over the fixed field and a conjugacy class over the original base field.
--
--   Source: the [Tau Ceti contributors](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/Chebotarev/PrimeCounting/FixedFieldContraction.lean#L223-L249) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`).
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/Chebotarev/PrimeCounting/FixedFieldContraction.lean#L223-L249

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_Algebra_Group_Conj
import Definitions.Def_TauCeti_FieldTheory_Galois_FixedField
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Counting
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Prime_Psi
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Weight
import Definitions.Def_TauCeti_NumberTheory_Chebotarev_PrimeCounting_VonMangoldt
import Definitions.Def_TauCeti_NumberTheory_NumberField_ArtinSymbol
import Definitions.Def_TauCeti_NumberTheory_NumberField_AutomorphismAction
import Definitions.Def_TauCeti_Order_Northcott_Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Ring.Subgroup
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Data.ZMod.Units
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
import Mathlib.LinearAlgebra.Pi
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.DirichletDensity
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Northcott
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.DedekindDomain.SelmerGroup
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.UniformSpace.Real

section
set_option autoImplicit true
namespace TauCeti
end TauCeti
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Contracting Frobenius `ϑ` and `ψ` from a cyclic fixed field

Let `L / K` be a finite Galois extension of number fields, let `C` be a conjugacy class of
`Gal(L/K)`, choose `sigma ∈ C`, and put `E = L ^ <sigma>`.  This file proves the exact identity

```text
∑_{𝔓 ∈ S_E, N 𝔓 ≤ x} log N 𝔓 = (#G / (#C * orderOf sigma)) * ϑ_C(x),
```

where `S_E` is the set of primes `𝔓` of `E` whose relative Artin class in `L / E` is represented by
`sigma`, that do not lie above `ramifiedPrimes K L`, and that have residue degree one over `K`.

There is no error term.  Away from the ramified primes, a prime `𝔓` of the relative fibre has
residue degree one over `K` exactly when the prime `𝔭` of `K` below it lies in the Frobenius fibre
of `C` (`NumberField.Chebotarev.inertiaDeg_eq_one_iff_under_mem_frobeniusPrimeSet`); then
`N 𝔓 = N 𝔭`, and over each such `𝔭` there are exactly `#G / (#C * orderOf sigma)` of them
(`NumberField.Chebotarev.fixedField_frobenius_fiber_card`).

The identity concerns `ϑ` at residue degree one only.  The other primes of the relative fibre have
residue degree at least two over `ℚ` or lie above `ramifiedPrimes K L`, so they are majorized by
the unrestricted sums appearing in `NumberField.Chebotarev.frobeniusDiscard_isLittleO` over
`L ^ <sigma>`.  In general there is no such identity for `ψ`: a prime power `𝔓 ^ m` with `m ≥ 2`
is selected by the `m`-th power of its Frobenius, and the prime of `K` below it need not have
class `C`.  So the transfer of `ψ` is only asymptotic,

```text
ψ_sigma^{L/E}(x) = (#G / (#C * orderOf sigma)) * ψ_C^{L/K}(x) + o(x),
```

obtained by removing the prime powers with `m ≥ 2` on both sides, applying the exact identity to
what remains, and discarding the relative primes of higher residue degree or above
`ramifiedPrimes K L`.

## Main results

* `NumberField.Chebotarev.primeTheta_fixedField_eq_mul_frobeniusTheta`: the residue-degree-one
  part of the relative Frobenius `ϑ` over `L ^ <sigma>`, away from the primes above
  `ramifiedPrimes K L`, is the fixed-field multiplicity times `frobeniusTheta K L C`.
* `NumberField.Chebotarev.frobeniusPsi_fixedField_sub_mul_frobeniusPsi_isLittleO`: the relative
  Frobenius `ψ` of `sigma` over `L ^ <sigma>` is the fixed-field multiplicity times
  `frobeniusPsi K L C`, up to `o(x)`.
* `NumberField.Chebotarev.frobeniusPsi_fixedField_asymptotic_iff`: hence the relative Frobenius
  `ψ` of `sigma` is `δ x + o(x)` exactly when `frobeniusPsi K L C` is `δ x + o(x)` divided by
  the fixed-field multiplicity.
* `NumberField.Chebotarev.frobeniusPsi_asymptotic_of_fixedField`: its specialisation at the cyclic
  value `δ = 1 / orderOf sigma`, which lands the Chebotarev value `#C / #G` over `K`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
* S. Lang, *Algebraic Number Theory*, Chapter I, §5.
-/

 section

open _root_.Filter _root_.IntermediateField
open scoped _root_.Asymptotics _root_.NumberField
open _root_.IsDedekindDomain (HeightOneSpectrum)

namespace NumberField.Chebotarev
end NumberField.Chebotarev
section NumberField.Chebotarev
open NumberField NumberField.Chebotarev

open _root_.TauCeti

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

theorem NumberField.Chebotarev.frobeniusPsi_fixedField_asymptotic_iff (C : _root_.ConjClasses (L ≃ₐ[K] L))
    (sigma : L ≃ₐ[K] L) (hsigma : sigma ∈ C.carrier) {δ : ℝ} :
    (fun x : ℝ ↦ _root_.NumberField.Chebotarev.frobeniusPsi ↥(_root_.IntermediateField.fixedField (_root_.Subgroup.zpowers sigma)) L
        (_root_.ConjClasses.mk sigma.toFixedFieldAlgEquiv) x - δ * x) =o[_root_.Filter.atTop] (fun x : ℝ ↦ x) ↔
      (fun x : ℝ ↦ _root_.NumberField.Chebotarev.frobeniusPsi K L C x -
        δ / ((_root_.Nat.card (L ≃ₐ[K] L) / (_root_.Nat.card C.carrier * _root_.orderOf sigma) : ℕ) : ℝ) * x)
          =o[_root_.Filter.atTop] (fun x : ℝ ↦ x) := by sorry
