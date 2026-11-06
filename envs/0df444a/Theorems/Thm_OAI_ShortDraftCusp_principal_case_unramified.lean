-- Prove2me | Theorems.Thm_OAI_ShortDraftCusp_principal_case_unramified
-- name    : OAI.ShortDraftCusp.principal_case_unramified
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:33:05.973629+00:00
-- url     : https://prove2.me/theorems/34afe8ad-7351-4fc6-ac9c-2f254caef54e
-- title:
--   Short Draft Cusp: principal case unramified
-- statement:
--   The Short Draft Cusp construction uses the principal case unramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Cusp/MatrixPhases.lean#L75-L84
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Cusp/MatrixPhases.lean#L75-L84

import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_MatrixPhases
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
open OAI.ShortDraftCusp
variable {R : Type*} [CommRing R]

theorem OAI.ShortDraftCusp.principal_case_unramified (a b c d u : R)
    (hdet : a * d - b * c = 1)
    (hc : c = 1) (hd : d = 0) (hu : u = a) :
    (!![-b,a + u * b;-d,c + u * d] : Matrix (Fin 2) (Fin 2) R) = 1 := by sorry
