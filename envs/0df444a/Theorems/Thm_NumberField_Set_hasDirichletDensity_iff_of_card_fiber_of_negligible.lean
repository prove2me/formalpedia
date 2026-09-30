-- Prove2me | Theorems.Thm_NumberField_Set_hasDirichletDensity_iff_of_card_fiber_of_negligible
-- name    : NumberField.Set.hasDirichletDensity_iff_of_card_fiber_of_negligible
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:12:07.467645+00:00
-- url     : https://prove2.me/theorems/66caafeb-98ab-4eea-b8f5-78aa370bccc9
-- title:
--   Dirichlet densities along a fibre count off a negligible set
-- statement:
--   Let $K,E$ be number fields, let $S$ and $T$ be sets of nonzero prime ideals of $\mathcal O_K$ and $\mathcal O_E$, respectively, and let $\pi$ map the primes of $E$ to those of $K$. Norms are absolute norms in the respective fields. Let $Z$ be a density-zero set of primes of $K$. Away from $\pi^{-1}(Z)$, assume $\pi$ sends $T$ into $S\setminus Z$ and preserves norms. Over $Z$, assume $N(\pi(Q))\le N(Q)$ for $Q\in T$. Suppose every $P\in S\setminus Z$ has exactly $c\ge1$ preimages in $T$, while each $P\in Z$ has at most $m$ such preimages for a fixed $m\in\mathbb N$. For every real $\delta$,
--
--   $$
--   \operatorname{dens}_D(T)=\delta\quad\Longleftrightarrow\quad\operatorname{dens}_D(S)=\frac\delta c.
--   $$
--
--   This transfers Dirichlet density through a uniform fibre count that is allowed a negligible exceptional set.
--
--   Source and proof credit: the Tau Ceti contributors, [original declaration and proof](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/Prime/Contraction.lean#L190-L226), Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`; adapted to Lean 4.33.1.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/ArithmeticDirichletSeries/Prime/Contraction.lean#L190-L226

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
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Contracting prime sums and Dirichlet densities along a fibre count

Let `K` and `E` be number fields, `T` a set of height-one primes of `𝓞 E` and `S` one of `𝓞 K`,
and let `π` send each prime of `E` to a prime of `K`. Suppose that `π` maps `T` into `S`, that it
preserves absolute norms on `T`, and that every `𝔭 ∈ S` has exactly `c ≠ 0` preimages in `T`.
Then, for every real `s`,

```text
∑_{𝔓 ∈ T} N𝔓 ^ (-s) = c * ∑_{𝔭 ∈ S} N𝔭 ^ (-s),
```

and consequently `T` has Dirichlet density `δ` exactly when `S` has Dirichlet density `δ / c`.

The fibre count only matters away from a set of density zero. If `π` does not increase norms and
has boundedly many preimages in `T` over each prime of `S`, the prime sum over `T` is bounded by a
multiple of the prime sum over `S`, so preimages of a density-zero set have density zero. Hence the
exact count `c` is needed only for the primes of `S` outside a density-zero set `Z`, with a
uniform bound over `Z`.

The typical `π` is contraction `𝔓 ↦ 𝔓 ∩ 𝓞 K` for an extension `E / K`. It preserves norms exactly
on the primes of residue degree one over `K`, and the others have density zero, so only primes of
residue degree one need to be counted in the fibres; at most `[E : K]` primes of `E` lie over a
given prime of `K`, which supplies the uniform bound over `Z`. This is how a density computed over
an extension field is transported down to the base, as in the proof of the Chebotarev density
theorem, where a relative Frobenius fibre over the fixed field of a cyclic subgroup is counted
over the primes of the base field.

## Main results

* `NumberField.Set.primeIdealZetaSum_eq_mul_of_card_fiber`: the exact identity of prime sums.
* `NumberField.Set.hasDirichletDensity_iff_of_card_fiber`: the transfer of Dirichlet densities.
* `NumberField.Set.primeIdealZetaSum_le_mul_of_encard_fiber_le`: the prime-sum inequality for a
  bounded fibre count.
* `NumberField.Set.HasDirichletDensity.zero_of_encard_fiber_le`: density zero pulls back along a
  bounded fibre count.
* `NumberField.Set.hasDirichletDensity_iff_of_card_fiber_of_negligible`: the transfer of
  Dirichlet densities when the fibre count is exact only off a set of density zero.
* `NumberField.Set.hasDirichletDensity_contraction`: the transfer along contraction, counting only
  primes of residue degree one and only off a set of density zero.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
* J.-P. Serre, *A Course in Arithmetic*, Chapter VI, §4.1.
-/

 section

open Filter IsDedekindDomain NumberField
open scoped symmDiff Topology

namespace NumberField.Set
end NumberField.Set
section NumberField.Set
open NumberField NumberField.Set

variable {K E : Type*} [Field K] [NumberField K] [Field E] [NumberField E]
  {T : Set (HeightOneSpectrum (𝓞 E))} {S : Set (HeightOneSpectrum (𝓞 K))}
  {π : HeightOneSpectrum (𝓞 E) → HeightOneSpectrum (𝓞 K)} {c : ℕ}

theorem NumberField.Set.hasDirichletDensity_iff_of_card_fiber_of_negligible {Z : _root_.Set (_root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K))}
    (hZ : Z.HasDirichletDensity 0) (hmaps : _root_.Set.MapsTo π (T \ π ⁻¹' Z) (S \ Z))
    (hnorm : ∀ 𝔓 ∈ T \ π ⁻¹' Z, _root_.Ideal.absNorm 𝔓.asIdeal = _root_.Ideal.absNorm (π 𝔓).asIdeal)
    (hnorm_le : ∀ 𝔓 ∈ T ∩ π ⁻¹' Z, _root_.Ideal.absNorm (π 𝔓).asIdeal ≤ _root_.Ideal.absNorm 𝔓.asIdeal)
    (hc : c ≠ 0)
    (hfiber : ∀ 𝔭 ∈ S \ Z, _root_.Nat.card {𝔓 // π 𝔓 = 𝔭 ∧ 𝔓 ∈ T} = c) {m : ℕ}
    (hbound : ∀ 𝔭 ∈ Z, (T ∩ π ⁻¹' {𝔭}).encard ≤ m) {δ : ℝ} :
    T.HasDirichletDensity δ ↔ S.HasDirichletDensity (δ / c) := by sorry
