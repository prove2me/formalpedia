-- Prove2me | Theorems.Thm_NumberField_Chebotarev_sum_inv_mul_vonMangoldtTransform_galoisCharacterWeight_apply
-- name    : NumberField.Chebotarev.sum_inv_mul_vonMangoldtTransform_galoisCharacterWeight_apply
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:32:49.124192+00:00
-- url     : https://prove2.me/theorems/48adc90c-5ecd-44f8-856f-4bdd38e00d22
-- title:
--   Character orthogonality for ideal von Mangoldt weights
-- statement:
--   Let $L/K$ be a finite abelian extension of number fields, with group $G$, and let $\sigma\in G$. For a nonzero integral ideal $I$, let $\Lambda_\chi(I)$ be the character-weighted von Mangoldt function: at an unramified prime power $I=\mathfrak p^j$ it is $\chi(\operatorname{Frob}_{\mathfrak p})^j\log N\mathfrak p$, and it is zero otherwise. Let $\Lambda_\sigma(I)$ be $\log N\mathfrak p$ when $I=\mathfrak p^j$ is unramified and $\operatorname{Frob}_{\mathfrak p}^{\,j}=\sigma$, and zero otherwise. Then
--
--   $$
--   \sum_{\chi\in\widehat G}\chi(\sigma)^{-1}\Lambda_\chi(I)=|G|\Lambda_\sigma(I),
--   $$
--
--   where $\widehat G$ is the set of complex multiplicative characters of $G$.
--
--   This converts an individual Frobenius condition into a finite character sum.
--
--   Source: the [Tau Ceti contributors](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/Chebotarev/PrimeCounting/CharacterExpansion.lean#L79-L130) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`).
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/Chebotarev/PrimeCounting/CharacterExpansion.lean#L79-L130

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_Algebra_Group_Conj
import Definitions.Def_TauCeti_GroupTheory_FiniteAbelian_CharacterOrthogonality
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Basic
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Counting
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Prime_Psi
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_VonMangoldt
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Weight
import Definitions.Def_TauCeti_NumberTheory_Chebotarev_GaloisCharacter_Weight
import Definitions.Def_TauCeti_NumberTheory_Chebotarev_PrimeCounting_VonMangoldt
import Definitions.Def_TauCeti_NumberTheory_Chebotarev_RamifiedPrimes
import Definitions.Def_TauCeti_NumberTheory_NumberField_ArtinSymbol
import Definitions.Def_TauCeti_NumberTheory_NumberField_AutomorphismAction
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_RamificationLocus
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Ring.Subgroup
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.Separable
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Pi
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
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
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
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
# The Frobenius von Mangoldt series as a character sum of logarithmic derivatives

Let `L / K` be a finite **abelian** Galois extension of number fields with group `G`, and fix
`σ ∈ G`. For each character `χ : G →* ℂˣ` let `L_χ` be the `L`-series of the Galois character
weight `MonoidHom.galoisCharacterWeight χ`, whose Euler product omits the primes ramified in `L`.
This file proves, for `Re s > 1`,

```text
∑_{𝔭 unramified, m ≥ 1, Frob(𝔭)^m = σ} log N𝔭 · N𝔭^{-ms}
  = (1 / #G) ∑_χ χ(σ)⁻¹ · (-L_χ'(s) / L_χ(s)).
```

The left-hand side is the `LSeries` of the canonical coefficient
`NumberField.Chebotarev.frobeniusVonMangoldtCoeff`, so the identity is a theorem about that
coefficient rather than a hypothesis on an arbitrary sequence. It reduces the
Frobenius-restricted von Mangoldt series to the logarithmic derivatives of the one-dimensional
character series, which is the form the Tauberian step of the Chebotarev argument consumes.

The proof is termwise. By
`TauCeti.MultiplicativeIdealWeight.logDeriv_LSeries_eq_neg_tsum_vonMangoldtTransform` each
`-L_χ'/L_χ` is the ideal-indexed series of `χ(A) Λ(A)`. At a prime power `A = 𝔭 ^ m` the
weight is `χ(Frob 𝔭) ^ m = χ(Frob(𝔭) ^ m)` when `𝔭` is unramified and `0` otherwise, and
character orthogonality
(`AlgEquiv.sum_inv_mul_galoisCharacterWeight_pow_apply_of_unramified`) collapses the character
sum at `A` to `#G` times the indicator of `Frob(𝔭) ^ m = σ`. That indicator is exactly the powered
filter of `frobeniusVonMangoldtWeight`, since in an abelian group the class of `Frob(𝔭) ^ m` is
`{σ}` precisely when `Frob(𝔭) ^ m = σ`.

## Main results

* `NumberField.Chebotarev.sum_inv_mul_vonMangoldtTransform_galoisCharacterWeight_apply`: the
  character sum of the von Mangoldt transforms at one nonzero ideal is `#G` times the Frobenius
  von Mangoldt weight of `σ` there.
* `NumberField.Chebotarev.LSeriesSummable_frobeniusVonMangoldtCoeff`: the Frobenius von Mangoldt
  series converges absolutely on `Re s > 1`, for an arbitrary conjugacy class.
* `NumberField.Chebotarev.LSeries_frobeniusVonMangoldtCoeff_eq_sum_logDeriv`: the character
  expansion of the Frobenius von Mangoldt series.

## Implementation notes

The inverse sits on the tag `σ`, never on the Frobenius argument. Writing `χ σ` for `(χ σ)⁻¹`, or
`χ (Frob 𝔭)⁻¹` for `χ (Frob 𝔭)`, replaces the fibre of `σ` by the fibre of `σ⁻¹`.

The prime-power filter uses the power of the Frobenius, not the Frobenius itself: the term at
`𝔭 ^ m` is counted when `Frob(𝔭) ^ m = σ`, even if `Frob 𝔭 ≠ σ`. This is what
`frobeniusVonMangoldtWeight` records and what the orthogonality at the `m`-th power of the weight
produces, so no separate bookkeeping of the higher prime powers is needed here.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
-/

 section

namespace NumberField.Chebotarev
end NumberField.Chebotarev
section NumberField.Chebotarev
open NumberField NumberField.Chebotarev

open _root_.TauCeti
open scoped _root_.nonZeroDivisors _root_.NumberField
open _root_.IsDedekindDomain (HeightOneSpectrum)

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

open scoped Classical IsMulCommutative

theorem NumberField.Chebotarev.sum_inv_mul_vonMangoldtTransform_galoisCharacterWeight_apply
    [_root_.IsMulCommutative (L ≃ₐ[K] L)] (σ : L ≃ₐ[K] L) (I : (_root_.Ideal (𝓞 K))⁰) :
    ∑ χ : (L ≃ₐ[K] L) →* ℂˣ, (((χ σ)⁻¹ : ℂˣ) : ℂ) *
        (_root_.MonoidHom.galoisCharacterWeight (L := L) χ).toIdealArithmeticFunction.vonMangoldtTransform
          I =
      (_root_.Nat.card (L ≃ₐ[K] L) : ℂ) * (_root_.NumberField.Chebotarev.frobeniusVonMangoldtWeight K L (_root_.ConjClasses.mk σ) I : ℂ) := by sorry
