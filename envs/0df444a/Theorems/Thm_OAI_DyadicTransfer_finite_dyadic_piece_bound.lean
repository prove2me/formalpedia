-- Prove2me | Theorems.Thm_OAI_DyadicTransfer_finite_dyadic_piece_bound
-- name    : OAI.DyadicTransfer.finite_dyadic_piece_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:15:52.966672+00:00
-- url     : https://prove2.me/theorems/0dbf854b-5667-4753-bfc5-d511cf281f70
-- title:
--   Dyadic Transfer: finite dyadic piece bound
-- statement:
--   The Dyadic Transfer construction uses the finite dyadic piece bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/PrimeExtraction.lean#L500-L548
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/PrimeExtraction.lean#L500-L548

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

theorem OAI.DyadicTransfer.finite_dyadic_piece_bound
    (F : ℕ → ℂ) (C r : ℝ) (hC : 0 ≤ C) (hr : 1 < r)
    (b : ℕ → ℝ) (hb : Summable b) (hb0 : ∀ m, 0 ≤ b m)
    (N M : ℕ)
    (hlow : ∀ k ≤ N, ‖F k‖ ≤ C * r ^ k)
    (hhigh : ∀ m, ‖F (N + 1 + m)‖ ≤ C * r ^ N * b m) :
    ‖∑ k ∈ Finset.range (N + 1 + M), F k‖ ≤
      C * (r ^ (N + 1) / (r - 1) + r ^ N * ∑' m, b m) := by sorry
