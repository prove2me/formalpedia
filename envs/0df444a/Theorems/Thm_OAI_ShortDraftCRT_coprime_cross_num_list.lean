-- Prove2me | Theorems.Thm_OAI_ShortDraftCRT_coprime_cross_num_list
-- name    : OAI.ShortDraftCRT.coprime_cross_num_list
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:16:50.255002+00:00
-- url     : https://prove2.me/theorems/7b64b1ac-c010-4caf-b22d-996a27319923
-- title:
--   Short Draft CRT: coprime cross num list
-- statement:
--   The Short Draft CRT construction uses the coprime cross num list property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ChineseRemainder/AdditiveCharacters.lean#L106-L120
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ChineseRemainder/AdditiveCharacters.lean#L106-L120

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

theorem OAI.ShortDraftCRT.coprime_cross_num_list (a c₀ : R) (rows : List (R × R))
    (hbase : IsCoprime a c₀) (hrows : GoodRows c₀ rows) :
    IsCoprime (crossNum a c₀ rows) (crossDen c₀ rows) := by sorry
