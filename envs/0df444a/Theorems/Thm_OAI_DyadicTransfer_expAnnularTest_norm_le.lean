-- Prove2me | Theorems.Thm_OAI_DyadicTransfer_expAnnularTest_norm_le
-- name    : OAI.DyadicTransfer.expAnnularTest_norm_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:15:54.578675+00:00
-- url     : https://prove2.me/theorems/1be0e0fb-9db2-4b21-b4be-589a36716805
-- title:
--   Dyadic Transfer: exp Annular Test norm le
-- statement:
--   The Dyadic Transfer construction uses the exp Annular Test norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/PrimeExtraction.lean#L448-L468
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/PrimeExtraction.lean#L448-L468

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_LocalEulerIdentities
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
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
open OAI.DyadicTransfer

theorem OAI.DyadicTransfer.expAnnularTest_norm_le (φ : ℝ → ℂ) (D : ℝ) (k : ℕ)
    (hD : 0 < D) (M : ℝ) (hM : ∀ y : ℝ, ‖annularCutoff φ y‖ ≤ M)
    {y : ℝ} (hy : 1 / 2 ≤ y) :
    ‖expAnnularTest φ D k y‖ ≤
      M * Real.exp (-((2 : ℝ) ^ k / D) / 2) := by sorry
