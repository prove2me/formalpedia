-- Prove2me | Theorems.Thm_OAI_ShortDraftCRT_addChar_crt_list_codifferent
-- name    : OAI.ShortDraftCRT.addChar_crt_list_codifferent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:31:45.546612+00:00
-- url     : https://prove2.me/theorems/2f42e6b4-f9de-4365-924b-8cd0fb62a3c4
-- title:
--   Short Draft CRT: add Char crt list codifferent
-- statement:
--   The Short Draft CRT construction uses the add Char crt list codifferent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ChineseRemainder/AdditiveCharacters.lean#L281-L338
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ChineseRemainder/AdditiveCharacters.lean#L281-L338

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

theorem OAI.ShortDraftCRT.addChar_crt_list_codifferent (ι : R →+* K) (ψ : AddChar K ℂ)
    (lam z : R) (ps : List R)
    (hlam : ι lam ≠ 0)
    (hperiod : ∀ y : R, ψ (ι y / ι lam) = 1)
    (hpair : ps.Pairwise IsCoprime)
    (hp : ∀ p ∈ ps, ι p ≠ 0) :
    ∃ ws : List R, ws.length = ps.length ∧
      ψ (ι z / (ι lam * ι ps.prod)) =
        (List.zipWith (fun p w => ψ (ι (w * z) / (ι lam * ι p))) ps ws).prod := by sorry
