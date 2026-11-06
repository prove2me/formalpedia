-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_sixth_power_rows_injective
-- name    : OAI.ActualEisensteinCubic.sixth_power_rows_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:21:55.867688+00:00
-- url     : https://prove2.me/theorems/ab40bb4b-6f8e-41d1-9063-a8321fd652b5
-- title:
--   Actual Eisenstein Cubic: sixth power rows injective
-- statement:
--   The Actual Eisenstein Cubic construction uses the sixth power rows injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/QuadraticTrace.lean#L109-L122
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/QuadraticTrace.lean#L109-L122

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
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

theorem OAI.ActualEisensteinCubic.sixth_power_rows_injective
    {ι : Type*} (S : Finset ι) (P : ι → Ideal O) (p : ι → O)
    (hprime : ∀ i ∈ S, (P i).IsMaximal)
    (hgen : ∀ i ∈ S, P i = Ideal.span {p i})
    (hinj : Set.InjOn P (S : Set ι)) :
    Set.InjOn (fun i => p i ^ 6) (S : Set ι) := by sorry
