-- Prove2me | Theorems.Thm_NumberField_Chebotarev_frobeniusPsi_asymptotic_of_mul_comm
-- name    : NumberField.Chebotarev.frobeniusPsi_asymptotic_of_mul_comm
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:14:51.111632+00:00
-- url     : https://prove2.me/theorems/0abe7631-e579-4c82-b036-0821cc72495f
-- title:
--   Weighted Chebotarev for abelian extensions
-- statement:
--   Let $L/K$ be a finite abelian extension of number fields and let $\sigma\in G=\operatorname{Gal}(L/K)$. For an extension $B/A$ and a conjugacy class $D$, write $\psi_{B/A,D}(x)$ for the sum of $\log N\mathfrak p$ over unramified prime powers $\mathfrak p^j$ with $j\ge1$, $N\mathfrak p^j\le x$, and $\operatorname{Frob}_{\mathfrak p}^{\,j}\in D$. Then, as $x\to+\infty$,
--
--   $$
--   \psi_{L/K,[\sigma]}(x)=\frac{x}{|G|}+o(x).
--   $$
--
--   This gives the asymptotic weighted distribution of each Frobenius element in the stated family of extensions.
--
--   Source: the [Tau Ceti contributors](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/Chebotarev/PrimeCounting/Chebotarev.lean#L159-L189) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`).
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/Chebotarev/PrimeCounting/Chebotarev.lean#L159-L189

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_Algebra_Group_Conj
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Counting
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Prime_Psi
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Weight
import Definitions.Def_TauCeti_NumberTheory_Chebotarev_PrimeCounting_VonMangoldt
import Definitions.Def_TauCeti_NumberTheory_NumberField_ArtinSymbol
import Definitions.Def_TauCeti_NumberTheory_NumberField_AutomorphismAction
import Definitions.Def_TauCeti_Order_Northcott_Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.Indicator
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Algebra.Order.Ring.Units
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Algebra.Ring.Subgroup
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Int.WithZero
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.Normal.Defs
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.DirichletDensity
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.ExistsRamified
import Mathlib.NumberTheory.NumberField.FractionalIdeal
import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Northcott
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.DedekindDomain.AdicValuation
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
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.MetricSpace.Pseudo.Real
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.UniformSpace.Real
import Mathlib.Topology.UniformSpace.UniformApproximation

section
set_option autoImplicit true
namespace TauCeti
end TauCeti
namespace TauCeti.NumberField
end TauCeti.NumberField
namespace TauCeti.NumberField.Chebotarev
end TauCeti.NumberField.Chebotarev
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The Chebotarev density theorem, for Chebyshev's `ψ`

Let `L / K` be a finite Galois extension of number fields with group `G`, and let `C` be a
conjugacy class of `G`. This file proves the prime-number-theorem form of Chebotarev's theorem,

```text
ψ_C(x) = (#C / #G) x + o(x),
```

where `ψ_C = frobeniusPsi K L C` sums `log N𝔭` over the prime powers `𝔭 ^ j` of `K` with `𝔭`
unramified in `L` and `Frob(𝔭) ^ j ∈ C`.

The proof is the weighted form of the cyclotomic crossing behind
`NumberField.Chebotarev.hasDirichletDensity_frobeniusPrimeSet`; in particular, the tagged-class
crossing follows the proof of `NumberField.Chebotarev.hasDirichletDensity_abelianFrobenius`.

* For abelian `G` and `σ ∈ G` of order `f`, pick an auxiliary prime `q` with `f ^ r ∣ q - 1`
  and cross with `M = L(μ_q)`, so that `Gal(M/K) ≃ G × (ZMod q)ˣ`. For each tag `τ` with
  `f ∣ orderOf τ`, the field `E_τ` fixed by `(σ, τ)` has `M` as a `q`-th cyclotomic extension,
  so the cyclotomic weighted theorem over `E_τ` and the contraction across the cyclic fixed field
  give `ψ_{(σ, τ)}(x) = x / #Gal(M/K) + o(x)` over `K`. The tagged classes are distinct classes
  over the class of `σ`, so their `ψ` functions add up to at most `ψ_σ`: for a fixed `q`, the
  limit in `x` gives `liminf ψ_σ(x) / x ≥ (1 - 2 ^ (-r)) ^ #f.primeFactors / #G`, and only then
  does `r` grow, giving `liminf ψ_σ(x) / x ≥ 1 / #G`.
* The `ψ` functions of all classes add up to `ψ_K(x) = x + o(x)` up to `O(log x)`, so these
  lower bounds saturate the total and each of them is the limit.
* For a general class `C ∋ σ`, the extension `L / L ^ ⟨σ⟩` is cyclic, and the contraction across
  the cyclic fixed field carries the abelian result down to `C`.

## Main results

* `NumberField.Chebotarev.frobeniusPsi_asymptotic_of_mul_comm`: for abelian `G` and `σ ∈ G`,
  `ψ_σ(x) = x / #G + o(x)`.
* `NumberField.Chebotarev.frobeniusPsi_asymptotic`: for every conjugacy class `C` of `G`,
  `ψ_C(x) = (#C / #G) x + o(x)`.
* `NumberField.Chebotarev.tendsto_frobeniusPsi`: the same, as `ψ_C(x) / x → #C / #G`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
* S. Lang, *Algebraic Number Theory*, Chapter XV.
* H. W. Lenstra Jr. and P. Stevenhagen, "Chebotarëv and his density theorem",
  *Math. Intelligencer* 18 (1996), 26–37, for the cyclotomic crossing.
-/

open _root_.Asymptotics _root_.Filter _root_.NumberField _root_.TauCeti _root_.TauCeti.NumberField.Chebotarev
open scoped _root_.NumberField _root_.TauCeti.NumberField _root_.Topology

namespace NumberField.Chebotarev
end NumberField.Chebotarev
section NumberField.Chebotarev
open NumberField NumberField.Chebotarev

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

-- **One auxiliary prime.** In an abelian extension, the Frobenius `ψ` of `σ` eventually exceeds
-- `δ x` for every `δ` below `(1 - 2 ^ (-r)) ^ #(orderOf σ).primeFactors / #G`, for every `r ≥ 1`.


-- Letting the level of the auxiliary prime grow: in an abelian extension, the Frobenius `ψ` of
-- `σ` eventually exceeds `δ x` for every `δ < 1 / #G`.


 section

theorem NumberField.Chebotarev.frobeniusPsi_asymptotic_of_mul_comm (hab : ∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ)
    (σ : L ≃ₐ[K] L) :
    (fun x : ℝ ↦ _root_.NumberField.Chebotarev.frobeniusPsi K L (_root_.ConjClasses.mk σ) x -
      (1 / _root_.Nat.card (L ≃ₐ[K] L) : ℝ) * x) =o[_root_.Filter.atTop] fun x : ℝ ↦ x := by sorry
