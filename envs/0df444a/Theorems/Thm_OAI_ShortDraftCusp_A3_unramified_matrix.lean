-- Prove2me | Theorems.Thm_OAI_ShortDraftCusp_A3_unramified_matrix
-- name    : OAI.ShortDraftCusp.A3_unramified_matrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:17:28.787391+00:00
-- url     : https://prove2.me/theorems/ca2fe6eb-663c-4503-bef2-b62fcf1ce12c
-- title:
--   Short Draft Cusp: A3 unramified matrix
-- statement:
--   The Short Draft Cusp construction uses the A3 unramified matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/RamifiedTracePhase.lean#L479-L482
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/RamifiedTracePhase.lean#L479-L482

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
open OAI.ShortDraftCusp
variable {R : Type*} [CommRing R]

theorem OAI.ShortDraftCusp.A3_unramified_matrix (a b c d u : R) :
    cuspMatrix a b c d * unramifiedHInv u =
      !![-b,a + u * b;-d,c + u * d] := by sorry
