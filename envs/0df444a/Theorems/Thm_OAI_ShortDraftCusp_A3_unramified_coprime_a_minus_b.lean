-- Prove2me | Theorems.Thm_OAI_ShortDraftCusp_A3_unramified_coprime_a_minus_b
-- name    : OAI.ShortDraftCusp.A3_unramified_coprime_a_minus_b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:19:38.096209+00:00
-- url     : https://prove2.me/theorems/2610e4e8-eedf-4de1-a4b9-02a277013c40
-- title:
--   Short Draft Cusp: A3 unramified coprime a minus b
-- statement:
--   The Short Draft Cusp construction uses the A3 unramified coprime a minus b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/LatticeCount.lean#L182-L185
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/LatticeCount.lean#L182-L185

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RamifiedTracePhase
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount
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
open OAI.ShortDraftCusp
variable {R : Type*} [CommRing R]

theorem OAI.ShortDraftCusp.A3_unramified_coprime_a_minus_b (a b c d : R)
    (hdet : a * d - b * c = 1) : IsCoprime a (-b) := by sorry
