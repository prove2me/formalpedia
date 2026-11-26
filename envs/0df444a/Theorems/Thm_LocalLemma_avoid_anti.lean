-- Prove2me | Theorems.Thm_LocalLemma_avoid_anti
-- name    : LocalLemma.avoid_anti
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:21:05.943797+00:00
-- url     : https://prove2.me/theorems/b2395751-e921-5f3e-b46e-54ce47148989
-- title:
--   Local Lemma: avoid anti
-- statement:
--   The Local Lemma construction uses the avoid anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/lovasz-local-lemma/blob/9d020fa8fb20e9426c2d6780a3cfab4a68794d89/LocalLemmaLib/LocalLemma.lean#L55-L59
-- source:
--   https://github.com/jtraverso/lovasz-local-lemma/blob/9d020fa8fb20e9426c2d6780a3cfab4a68794d89/LocalLemmaLib/LocalLemma.lean#L55-L59

module
public import Mathlib
public import Definitions.Def_LocalLemmaLib_Coin
public import Definitions.Def_LocalLemmaLib_LocalLemma
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory
open LocalLemma

theorem LocalLemma.avoid_anti {Ω : Type*} {n : ℕ} (A : Fin n → Set Ω) {S T : Finset (Fin n)} (h : S ⊆ T) :
    avoid A T ⊆ avoid A S := by sorry
