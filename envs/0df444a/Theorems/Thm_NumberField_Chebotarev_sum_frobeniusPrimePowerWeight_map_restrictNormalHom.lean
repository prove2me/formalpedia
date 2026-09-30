-- Prove2me | Theorems.Thm_NumberField_Chebotarev_sum_frobeniusPrimePowerWeight_map_restrictNormalHom
-- name    : NumberField.Chebotarev.sum_frobeniusPrimePowerWeight_map_restrictNormalHom
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:08:28.304536+00:00
-- url     : https://prove2.me/theorems/8123fe68-6432-43b2-b368-f84078dc9933
-- title:
--   Restriction and summation of Frobenius prime-power weights
-- statement:
--   Let $K\subseteq M\subseteq L$ be number fields with $L/K$ and $M/K$ Galois, let $C$ be a conjugacy class in $\operatorname{Gal}(M/K)$, and let $A=\mathfrak p^j$ with $j\ge1$. For an extension $B/K$, let $w_{B,D}(A)$ be $\log N\mathfrak p$ when $\mathfrak p$ is unramified in $B$ and its $j$-th Frobenius power belongs to $D$, and zero otherwise. Then
--
--   $$
--   \sum_{D:\operatorname{res}(D)=C}w_{L,D}(A)
--   =\mathbf1_{\mathfrak p\text{ unramified in }L}\,w_{M,C}(A).
--   $$
--
--   The sum is over conjugacy classes of $\operatorname{Gal}(L/K)$ and $\operatorname{res}$ is restriction to $M$.
--
--   This describes compatibility of the weighted Frobenius partition with normal subextensions, including primes that ramify upstairs.
--
--   Source: the [Tau Ceti contributors](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/Chebotarev/PrimeCounting/Tower.lean#L69-L117) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`).
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/Chebotarev/PrimeCounting/Tower.lean#L69-L117

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
# Frobenius `ψ` along a normal subextension

Let `K ⊆ M ⊆ L` be number fields with `L / K` and `M / K` Galois. Restriction to `M` is a group
homomorphism `Gal(L/K) → Gal(M/K)`, it carries the Artin class of a prime `𝔭` of `𝓞 K` to the
Artin class of `𝔭` for `M / K` with no power taken
(`NumberField.artinSymbol_map_restrictNormalHom`), and it commutes with powers of conjugacy
classes. So a prime power `𝔭 ^ j` counted by `frobeniusPsi K L D` for a class `D` of `Gal(L/K)` is
counted by `frobeniusPsi K M C` for the single class `C = ConjClasses.map _ D`, and the classes `D`
lying over a fixed `C` contribute to it disjointly.

This file records that refinement. Pointwise, the Frobenius weights of the classes over `C` add up
to the Frobenius weight of `C` itself, except at prime powers based at a prime ramifying in `L`,
where the upper weights all vanish while the lower one need not. Summing over prime powers, any
family of distinct classes over `C` gives a lower bound for `frobeniusPsi K M C`, and the full
family misses only the finitely many primes of `ramifiedPrimes K L`, hence accounts for
`frobeniusPsi K M C` up to `O(log x)`.

The lower bound is the shape the cyclotomic crossing consumes: over the compositum `M(μ_q)` of `M`
with an auxiliary cyclotomic field, the classes of the tagged elements `(σ, τ)` for distinct `τ`
are distinct classes over the class of `σ`, so the weighted asymptotics of their fibres add up to a
lower bound for the weighted asymptotics of the fibre of `σ`.

There is no companion upper bound for a proper subfamily, and none is needed: the crossing closes
by summing the lower bounds over all of `Gal(M/K)` against `ψ_M`, which
`NumberField.Chebotarev.primePsi_univ_sub_sum_frobeniusPsi_isBigO_log` supplies.

## Main results

* `NumberField.Chebotarev.sum_frobeniusPrimePowerWeight_map_restrictNormalHom`: at a single prime
  power, the Frobenius weights of the classes of `Gal(L/K)` over `C` add up to the Frobenius weight
  of `C`, unless the base ramifies in `L`, in which case they add up to `0`.
* `NumberField.Chebotarev.sum_frobeniusPsi_le_frobeniusPsi`: the Frobenius `ψ` functions of any
  finite family of distinct classes over `C` add up to at most `frobeniusPsi K M C`.
* `NumberField.Chebotarev.frobeniusPsi_sub_sum_frobeniusPsi_le_primePsi`: over the full family,
  the defect is at most `ψ` of the finite set `ramifiedPrimes K L`.
* `NumberField.Chebotarev.frobeniusPsi_sub_sum_frobeniusPsi_isBigO_log`: hence the defect is
  `O(log x)`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §9 and Chapter VII, §13.
* R. Sharifi, *Algebraic Number Theory*, the proof of Theorem 7.2.2, where the weighted count over
  an auxiliary compositum is bounded by the weighted count downstairs.
-/

 section

namespace NumberField.Chebotarev
end NumberField.Chebotarev
section NumberField.Chebotarev
open NumberField NumberField.Chebotarev

open Filter TauCeti
open scoped Asymptotics NumberField
open IsDedekindDomain (HeightOneSpectrum)

variable {K L M : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Field M]
  [NumberField M] [Algebra K L] [Algebra K M] [Algebra M L] [IsScalarTower K M L] [IsGalois K L]
  [IsGalois K M]

open scoped Classical

theorem NumberField.Chebotarev.sum_frobeniusPrimePowerWeight_map_restrictNormalHom (C : _root_.ConjClasses (M ≃ₐ[K] M))
    (A : _root_.TauCeti.IdealPrimePower K) :
    ∑ D ∈ {D : _root_.ConjClasses (L ≃ₐ[K] L) |
        ConjClasses.map (_root_.AlgEquiv.restrictNormalHom M) D = C},
        _root_.NumberField.Chebotarev.frobeniusPrimePowerWeight K L D A =
      {B : _root_.TauCeti.IdealPrimePower K | primePowerBase B ∉ _root_.NumberField.Chebotarev.ramifiedPrimes K L}.indicator
        (_root_.NumberField.Chebotarev.frobeniusPrimePowerWeight K M C) A := by sorry
