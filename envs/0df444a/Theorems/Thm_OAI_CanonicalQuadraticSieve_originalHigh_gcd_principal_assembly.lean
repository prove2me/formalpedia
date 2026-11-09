-- Prove2me | Theorems.Thm_OAI_CanonicalQuadraticSieve_originalHigh_gcd_principal_assembly
-- name    : OAI.CanonicalQuadraticSieve.originalHigh_gcd_principal_assembly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-08T19:50:42.926041+00:00
-- url     : https://prove2.me/theorems/82d9fb41-17ca-4e3b-893c-0201164940a6
-- title:
--   Canonical Quadratic Sieve: original High gcd principal assembly
-- statement:
--   The Canonical Quadratic Sieve construction uses the original High gcd principal assembly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/CommonMasks.lean#L447-L486
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/CommonMasks.lean#L447-L486

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CuspCoercivity
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CommonMasks
set_option autoImplicit false
open OAI
noncomputable section
open OAI.CanonicalQuadraticSieve
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson

theorem OAI.CanonicalQuadraticSieve.originalHigh_gcd_principal_assembly {n : Type} [Fintype n] [DecidableEq n]
    (D : Ideal O) (hD : D≠0) (cols : n → Ideal O) (hcols : ∀ j, Admissible (cols j))
    (hdiv : ∀ j, D∣cols j) (hproper : ∀ j, cols j≠D)
    (hray : ∀ j k, columnRay (cols j)=columnRay (cols k))
    (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) (M K : ℝ) (hM : 0<M) :
    (∑ j, ∑ k, if gcd (cols j) (cols k)=D then
      star (a j)*a k*(∑' lengthScale : Ideal O, originalPairHigh (cols j) (cols k) W M K lengthScale) else 0) =
      (∑ q ∈ idealDivisors (commonMaskIdeal D), (UniqueFactorizationMonoid.moebius q:ℂ)*
        retainedDualPrincipalSum (quadraticTransformedSquareProfile W)
          (fun I : squarefreeIdealRange K => I.val) (fun j => idealQuotient D (cols j))
          (fun j => a j*quadraticRow (idealQuotient D (cols j)) (idealGenerator q)) M (Ideal.absNorm q:ℝ)) +
      maskedDualTailFamily (commonMaskIdeal D) (fun j => idealQuotient D (cols j)) a W M K -
      (6:ℂ)⁻¹ * maskedPrincipalSourceSum (commonMaskIdeal D) (quadraticSquareProfile W)
        (fun B : coprimeSquarefreeRange (commonMaskIdeal D) K => B.val)
        (fun j => idealQuotient D (cols j)) a M := by sorry
