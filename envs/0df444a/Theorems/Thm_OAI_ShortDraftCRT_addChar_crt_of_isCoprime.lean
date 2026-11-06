-- Prove2me | Theorems.Thm_OAI_ShortDraftCRT_addChar_crt_of_isCoprime
-- name    : OAI.ShortDraftCRT.addChar_crt_of_isCoprime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:16:44.173091+00:00
-- url     : https://prove2.me/theorems/d5b0365b-39c6-4e0e-9ba4-c75dde00f459
-- title:
--   Short Draft CRT: add Char crt of is Coprime
-- statement:
--   The Short Draft CRT construction uses the add Char crt of is Coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ChineseRemainder/AdditiveCharacters.lean#L29-L40
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ChineseRemainder/AdditiveCharacters.lean#L29-L40

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

theorem OAI.ShortDraftCRT.addChar_crt_of_isCoprime
    {R : Type*} [CommRing R] (ι : R →+* K) (ψ : AddChar K ℂ)
    (m n : R) (z : K)
    (hcop : IsCoprime n m) (hm : ι m ≠ 0) (hn : ι n ≠ 0) :
    ∃ u v : R,
      u * n + v * m = 1 ∧
      ψ (z / (ι m * ι n)) =
        ψ (ι u * z / ι m) * ψ (ι v * z / ι n) := by sorry
