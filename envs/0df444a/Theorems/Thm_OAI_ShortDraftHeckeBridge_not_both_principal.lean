-- Prove2me | Theorems.Thm_OAI_ShortDraftHeckeBridge_not_both_principal
-- name    : OAI.ShortDraftHeckeBridge.not_both_principal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:49:54.975973+00:00
-- url     : https://prove2.me/theorems/4f5ba557-248b-4dd8-9ab5-20bf587a2c27
-- title:
--   Short Draft Hecke Bridge: not both principal
-- statement:
--   The Short Draft Hecke Bridge construction uses the not both principal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/NormFiberMellin.lean#L271-L280
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/NormFiberMellin.lean#L271-L280

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
open OAI.ShortDraftHeckeBridge

theorem OAI.ShortDraftHeckeBridge.not_both_principal {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    ¬ ((χ.changeLevel (Nat.dvd_mul_right q 3) = 1) ∧
      χ.changeLevel (Nat.dvd_mul_right q 3) *
        chiMinusThree.changeLevel (Nat.dvd_mul_left 3 q) = 1) := by sorry
