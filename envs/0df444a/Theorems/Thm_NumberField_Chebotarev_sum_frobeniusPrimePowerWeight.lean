-- Prove2me | Theorems.Thm_NumberField_Chebotarev_sum_frobeniusPrimePowerWeight
-- name    : NumberField.Chebotarev.sum_frobeniusPrimePowerWeight
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:46:56.028978+00:00
-- url     : https://prove2.me/theorems/1d5a15ec-11c7-46d1-84ed-1a88b430e8bb
-- title:
--   Partition of prime-power weights by Frobenius class
-- statement:
--   Let $L/K$ be a finite Galois extension of number fields. For a prime power $A=\mathfrak p^j$ with $j\ge1$, define $w_C(A)=\log N\mathfrak p$ if $\mathfrak p$ is unramified in $L$ and its arithmetic Frobenius satisfies $\operatorname{Frob}_{\mathfrak p}^{\,j}=C$ as a conjugacy class; otherwise set $w_C(A)=0$. Then
--
--   $$
--   \sum_{C\subset\operatorname{Gal}(L/K)}w_C(A)
--   =\begin{cases}\log N\mathfrak p,&\mathfrak p\text{ unramified in }L,\\0,&\mathfrak p\text{ ramified in }L.\end{cases}
--   $$
--
--   The sum ranges over all conjugacy classes.
--
--   This partitions the unramified von Mangoldt weight into its Frobenius components.
--
--   Source: the [Tau Ceti contributors](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/Chebotarev/PrimeCounting/Partition.lean#L57-L76) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`).
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/Chebotarev/PrimeCounting/Partition.lean#L57-L76

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_Algebra_Group_Conj
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Counting
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Prime_Psi
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Weight
import Definitions.Def_TauCeti_NumberTheory_Chebotarev_PrimeCounting_VonMangoldt
import Definitions.Def_TauCeti_NumberTheory_Chebotarev_RamifiedPrimes
import Definitions.Def_TauCeti_NumberTheory_NumberField_ArtinSymbol
import Definitions.Def_TauCeti_NumberTheory_NumberField_AutomorphismAction
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_RamificationLocus
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Ring.Subgroup
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.Separable
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Pi
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Northcott
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
# The Frobenius `ψ` fibres partition Chebyshev's `ψ`

Let `L / K` be a finite Galois extension of number fields with group `G`. A prime power `𝔭 ^ j`
with `𝔭` unramified in `L` lies in the powered Frobenius fibre of exactly one conjugacy class of
`G`, namely `(artinSymbol 𝔭) ^ j`, and a prime power based at a ramified prime lies in none. So the
Frobenius `ψ` functions of all conjugacy classes add up to Chebyshev's `ψ` of `K` with the ramified
primes removed:

```text
∑_C ψ_C(x) + ψ_{ramifiedPrimes K L}(x) = ψ_K(x),
```

and the correction is `O(log x)` because the ramified set is finite.

These identities supply the partition input for the weighted crossing. The later squeeze also
requires the cyclotomic weighted theorem and its consequence `ψ_K(x) / x → 1`.

## Main results

* `NumberField.Chebotarev.sum_frobeniusPrimePowerWeight`: at a single prime power, the Frobenius
  weights of all classes add up to the von Mangoldt weight if the base is unramified, and to `0`
  otherwise.
* `NumberField.Chebotarev.sum_frobeniusPsi_add_primePsi_ramifiedPrimes`: the Frobenius `ψ`
  functions and `ψ` of the ramified primes add up to `ψ_K`.
* `NumberField.Chebotarev.primePsi_univ_sub_sum_frobeniusPsi_isBigO_log`: the Frobenius `ψ`
  functions account for `ψ_K` up to `O(log x)`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
* S. Lang, *Algebraic Number Theory*, Chapter XV.
-/

 section

namespace NumberField.Chebotarev
end NumberField.Chebotarev
section NumberField.Chebotarev
open NumberField NumberField.Chebotarev

open _root_.Filter _root_.TauCeti
open scoped _root_.Asymptotics _root_.NumberField
open _root_.IsDedekindDomain (HeightOneSpectrum)

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

open scoped Classical 

variable (K L)

theorem NumberField.Chebotarev.sum_frobeniusPrimePowerWeight (A : _root_.TauCeti.IdealPrimePower K) :
    ∑ C : _root_.ConjClasses (L ≃ₐ[K] L), _root_.NumberField.Chebotarev.frobeniusPrimePowerWeight K L C A =
      {B : _root_.TauCeti.IdealPrimePower K | primePowerBase B ∉ _root_.NumberField.Chebotarev.ramifiedPrimes K L}.indicator
        _root_.TauCeti.primePowerWeight A := by sorry
