-- Prove2me | Theorems.Thm_LocalLemma_avoid_insert
-- name    : LocalLemma.avoid_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:21:10.294873+00:00
-- url     : https://prove2.me/theorems/c76ddfb5-cb87-4e53-b3d9-348758990872
-- title:
--   Local Lemma: avoid insert
-- statement:
--   The Local Lemma construction uses the avoid insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/lovasz-local-lemma/blob/9d020fa8fb20e9426c2d6780a3cfab4a68794d89/LocalLemmaLib/LocalLemma.lean#L51-L53
-- source:
--   https://github.com/jtraverso/lovasz-local-lemma/blob/9d020fa8fb20e9426c2d6780a3cfab4a68794d89/LocalLemmaLib/LocalLemma.lean#L51-L53

module
public import Mathlib
public import Definitions.Def_LocalLemmaLib_Coin
public import Definitions.Def_LocalLemmaLib_LocalLemma
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory
open LocalLemma

theorem LocalLemma.avoid_insert {Ω : Type*} {n : ℕ} (A : Fin n → Set Ω) (S : Finset (Fin n)) (j : Fin n) :
    avoid A (insert j S) = avoid A S \ A j := by sorry
