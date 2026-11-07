-- Prove2me | Theorems.Thm_OAI_ShortDraftHeckeBridge_normFiberExpSum_norm_le_exp
-- name    : OAI.ShortDraftHeckeBridge.normFiberExpSum_norm_le_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:49:14.681092+00:00
-- url     : https://prove2.me/theorems/b5355567-b39b-48e1-b002-72d6c7edf21b
-- title:
--   Short Draft Hecke Bridge: norm Fiber Exp Sum norm le exp
-- statement:
--   The Short Draft Hecke Bridge construction uses the norm Fiber Exp Sum norm le exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/NormFiberMellin.lean#L454-L509
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/NormFiberMellin.lean#L454-L509

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LocalNonvanishing
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_NormFiberMellin
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
open OAI.ShortDraftHeckeBridge

theorem OAI.ShortDraftHeckeBridge.normFiberExpSum_norm_le_exp
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → normFiberCoeff weight n = pairInverseCoeff χ ψ n)
    (ha0 : normFiberCoeff weight 0 = 0)
    (t : ℝ) (ht : 1 ≤ t) :
    ‖normFiberExpSum weight t‖ ≤
      (∑' n : ℕ, (n : ℝ) * Real.exp (-(n : ℝ) / 2)) *
        Real.exp (-t / 2) := by sorry
