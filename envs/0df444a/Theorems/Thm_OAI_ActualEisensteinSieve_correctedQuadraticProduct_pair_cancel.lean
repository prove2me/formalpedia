-- Prove2me | Theorems.Thm_OAI_ActualEisensteinSieve_correctedQuadraticProduct_pair_cancel
-- name    : OAI.ActualEisensteinSieve.correctedQuadraticProduct_pair_cancel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:32:42.117844+00:00
-- url     : https://prove2.me/theorems/edee2412-f925-4c5b-9800-60ba8f3e7fa8
-- title:
--   Actual Eisenstein Sieve: corrected Quadratic Product pair cancel
-- statement:
--   The Actual Eisenstein Sieve construction uses the corrected Quadratic Product pair cancel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/EisensteinIdeals.lean#L810-L832
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/EisensteinIdeals.lean#L810-L832

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
noncomputable section
open OAI.ActualEisensteinSieve

theorem OAI.ActualEisensteinSieve.correctedQuadraticProduct_pair_cancel
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : ι → Ideal O) (Q : κ → Ideal O)
    [∀ i, (P i).IsMaximal] [∀ j, (Q j).IsMaximal]
    (hsame : quadraticProduct P (-1) = quadraticProduct Q (-1))
    (x : O) (hx : x ∉ lambdaIdeal) :
    correctedQuadraticProduct P x * correctedQuadraticProduct Q x =
      quadraticProduct P x * quadraticProduct Q x := by sorry
