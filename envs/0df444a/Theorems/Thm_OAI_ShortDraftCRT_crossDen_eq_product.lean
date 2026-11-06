-- Prove2me | Theorems.Thm_OAI_ShortDraftCRT_crossDen_eq_product
-- name    : OAI.ShortDraftCRT.crossDen_eq_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:16:45.680031+00:00
-- url     : https://prove2.me/theorems/4025804d-fab9-404b-b991-efcf8c55fe77
-- title:
--   Short Draft CRT: cross Den eq product
-- statement:
--   The Short Draft CRT construction uses the cross Den eq product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ChineseRemainder/AdditiveCharacters.lean#L140-L147
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ChineseRemainder/AdditiveCharacters.lean#L140-L147

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open OAI.ShortDraftCRT
open AddChar
variable {K : Type*} [Field K]
variable {R : Type*} [CommRing R]

theorem OAI.ShortDraftCRT.crossDen_eq_product (c₀ : R) (rows : List (R × R)) :
    crossDen c₀ rows = c₀ * (rows.map Prod.fst).prod := by sorry
