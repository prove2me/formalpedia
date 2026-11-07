-- Prove2me | Theorems.Thm_OAI_ShortDraftHeckeBridge_norm_p_sq_fiber_split
-- name    : OAI.ShortDraftHeckeBridge.norm_p_sq_fiber_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:53:51.968672+00:00
-- url     : https://prove2.me/theorems/33f74d31-5c8c-4262-88fa-4dfd80a06e83
-- title:
--   Short Draft Hecke Bridge: norm p sq fiber split
-- statement:
--   The Short Draft Hecke Bridge construction uses the norm p sq fiber split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/NormFiberCharacters.lean#L392-L407
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/NormFiberCharacters.lean#L392-L407

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_NormFiberMellin
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_NormFiberCharacters
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

theorem OAI.ShortDraftHeckeBridge.norm_p_sq_fiber_split {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1) :
    {I : Ideal O | Ideal.absNorm I = p ^ 2} =
      {I : Ideal O | ∃ P Q : Ideal O,
        P ∈ (Ideal.span {(p : ℤ)}).primesOver O ∧
        Q ∈ (Ideal.span {(p : ℤ)}).primesOver O ∧
        I = P * Q} := by sorry
