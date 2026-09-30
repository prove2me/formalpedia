-- Prove2me | Theorems.Thm_NumberField_Set_HasDirichletDensity_of_symmDiff
-- name    : NumberField.Set.HasDirichletDensity.of_symmDiff
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:11:52.1605+00:00
-- url     : https://prove2.me/theorems/3d6cf347-d73a-4164-bc4e-6289f89678d1
-- title:
--   Sets of density zero are negligible
-- statement:
--   Let $K$ be a number field with ring of integers $\mathcal O_K$, and write $N(I)=|\mathcal O_K/I|$ for the norm of a nonzero integral ideal. Let $S,T$ be sets of nonzero prime ideals, and let $\delta\in\mathbb R$. If $T$ has Dirichlet density $\delta$ and its symmetric difference with $S$ has Dirichlet density zero, then
--
--   $$
--   \operatorname{dens}_D(T)=\delta,\quad\operatorname{dens}_D(S\mathbin\triangle T)=0\quad\Longrightarrow\quad\operatorname{dens}_D(S)=\delta.
--   $$
--
--   Dirichlet density is unchanged by an alteration supported on a density-zero set.
--
--   Source and proof credit: the Tau Ceti contributors, [original declaration and proof](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/DirichletDensity/Negligible.lean#L104-L127), Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`; adapted to Lean 4.33.1.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/DirichletDensity/Negligible.lean#L104-L127

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Indicator
import Mathlib.Algebra.Ring.Subgroup
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.LinearAlgebra.Pi
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.DirichletDensity
import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Northcott
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.UniformSpace.Real

section
set_option autoImplicit true
namespace TauCeti
end TauCeti
namespace TauCeti.NumberField
end TauCeti.NumberField
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Sets of primes of Dirichlet density zero

For a number field `K`, Mathlib's `NumberField.Set.HasDirichletDensity S δ` says that
`P_S(s) / P(s) → δ` as `s → 1⁺`, where `P_S(s) = ∑_{𝔭 ∈ S} N(𝔭) ^ (-s)` and `P` is the sum over
all height-one primes. Since `P(s) → ∞` as `s → 1⁺`
(`TauCeti.tendsto_primeIdealZetaSum_univ_atTop`), any set whose partial sum stays bounded near
`1` has Dirichlet density zero. This covers every finite set of primes, and every set whose
series `∑_{𝔭 ∈ S} N(𝔭)⁻¹` converges, such as the primes of residue degree greater than one.

A set of density zero is negligible: two sets whose symmetric difference has density zero have
the same Dirichlet density, or neither has one. In particular the Dirichlet density of a set of
primes does not change when finitely many primes are added or removed, or when the set is
restricted to the primes of residue degree one.

## Main results

* `NumberField.Set.hasDirichletDensity_zero_of_eventually_le`: a set whose partial sum is bounded
  as `s → 1⁺` has Dirichlet density zero.
* `NumberField.Set.hasDirichletDensity_zero_of_summable`: a set of primes with
  `∑_{𝔭 ∈ S} N(𝔭)⁻¹ < ∞` has Dirichlet density zero.
* `NumberField.Set.hasDirichletDensity_of_finite`: a finite set of primes has Dirichlet density
  zero, so a set of nonzero Dirichlet density is infinite
  (`NumberField.Set.HasDirichletDensity.infinite`).
* `NumberField.Set.hasDirichletDensity_iff_of_symmDiff`: sets whose symmetric difference has
  density zero have the same densities; `NumberField.Set.hasDirichletDensity_iff_of_finite_symmDiff`
  is the case of a finite symmetric difference.
* `TauCeti.hasDirichletDensity_higherDegreePrimes`: the primes of residue degree greater than one
  have Dirichlet density zero, and
  `TauCeti.hasDirichletDensity_inter_compl_higherDegreePrimes_iff` lets a density be computed on
  the primes of residue degree one alone.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter VI, §4.1.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
-/

 section

namespace NumberField.Set
end NumberField.Set
section NumberField.Set
open NumberField NumberField.Set

open _root_.Filter _root_.IsDedekindDomain _root_.NumberField _root_.TauCeti
open scoped _root_.NumberField _root_.TauCeti.NumberField _root_.symmDiff _root_.Topology

variable {K : Type*} [Field K] [NumberField K]
variable {S T : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ}

theorem NumberField.Set.HasDirichletDensity.of_symmDiff (hT : T.HasDirichletDensity δ)
    (h : (S ∆ T).HasDirichletDensity 0) : S.HasDirichletDensity δ := by sorry
