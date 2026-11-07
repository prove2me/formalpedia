-- Prove2me | Theorems.Thm_OAI_EisensteinSchwartzPoisson_actual_eisenstein_periodic_fourier
-- name    : OAI.EisensteinSchwartzPoisson.actual_eisenstein_periodic_fourier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:57:27.448825+00:00
-- url     : https://prove2.me/theorems/a24096b0-6f35-4bb2-b289-efe2346a7435
-- title:
--   Eisenstein Schwartz Poisson: actual eisenstein periodic fourier
-- statement:
--   The Eisenstein Schwartz Poisson construction uses the actual eisenstein periodic fourier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/EisensteinLattice.lean#L374-L393
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/EisensteinLattice.lean#L374-L393

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SecondPoissonScale
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_EisensteinLattice
import Theorems.Thm_OAI_ConcreteTraceCRT_finite_quotient_span

set_option autoImplicit false
open OAI
noncomputable section
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
open OAI.EisensteinSchwartzPoisson
open MeasureTheory EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open scoped FourierTransform SchwartzMap RealInnerProductSpace

theorem OAI.EisensteinSchwartzPoisson.actual_eisenstein_periodic_fourier (f : 𝓢(ℂ, ℂ)) (c : O) (hc : c ≠ 0)
    (P : O ⧸ Ideal.span {c} → ℂ) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) * f (eisEmbedding z)) =
      (2 / (Real.sqrt 3 * ‖eisEmbedding c‖ ^ 2)) • ∑' p : ℤ × ℤ,
        (∑ r : O ⧸ Ideal.span {c}, P r *
          (Real.fourierChar (inner ℝ
            (eisEmbedding (GaussianShiftedPartition.representative c r))
            (eisensteinDualFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)) : ℂ)) *
          (𝓕 f) (eisensteinDualFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p) := by sorry
