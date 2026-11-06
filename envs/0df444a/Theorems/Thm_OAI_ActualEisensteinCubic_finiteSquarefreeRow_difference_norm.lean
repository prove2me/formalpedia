-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_finiteSquarefreeRow_difference_norm
-- name    : OAI.ActualEisensteinCubic.finiteSquarefreeRow_difference_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:16:20.469586+00:00
-- url     : https://prove2.me/theorems/ffba1c77-13ff-4608-83dd-65e4caacf888
-- title:
--   Actual Eisenstein Cubic: finite Squarefree Row difference norm
-- statement:
--   The Actual Eisenstein Cubic construction uses the finite Squarefree Row difference norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/RamifiedTracePhase.lean#L365-L376
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/RamifiedTracePhase.lean#L365-L376

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_LocalProductAssembly
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RamifiedTracePhase
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
open OAI.ActualEisensteinCubic

theorem OAI.ActualEisensteinCubic.finiteSquarefreeRow_difference_norm
    {ι N : Type*} [DecidableEq N]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i)
    (columns : Finset N) (support : N → Finset ι)
    (weight : N → ℂ) (a : O) :
    ‖(∑ n ∈ columns, weight n) -
      (∑ n ∈ columns,
        weight n * finiteSquarefreeRow P hgood (support n) (a ^ 6))‖ ≤
      ∑ n ∈ columns.filter (fun n => ∃ i ∈ support n, a ∈ P i), ‖weight n‖ := by sorry
