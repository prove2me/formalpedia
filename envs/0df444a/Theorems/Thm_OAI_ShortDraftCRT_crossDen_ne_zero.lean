-- Prove2me | Theorems.Thm_OAI_ShortDraftCRT_crossDen_ne_zero
-- name    : OAI.ShortDraftCRT.crossDen_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:16:51.931192+00:00
-- url     : https://prove2.me/theorems/4fe23977-f606-452b-8477-6d3d9202117b
-- title:
--   Short Draft CRT: cross Den ne zero
-- statement:
--   The Short Draft CRT construction uses the cross Den ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ChineseRemainder/AdditiveCharacters.lean#L122-L138
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ChineseRemainder/AdditiveCharacters.lean#L122-L138

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

theorem OAI.ShortDraftCRT.crossDen_ne_zero (ι : R →+* K) (c₀ : R)
    (rows : List (R × R)) (hc₀ : ι c₀ ≠ 0)
    (hp : ∀ ph ∈ rows, ι ph.1 ≠ 0) :
    ι (crossDen c₀ rows) ≠ 0 := by sorry
