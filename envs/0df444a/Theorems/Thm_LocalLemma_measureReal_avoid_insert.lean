-- Prove2me | Theorems.Thm_LocalLemma_measureReal_avoid_insert
-- name    : LocalLemma.measureReal_avoid_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:21:03.833746+00:00
-- url     : https://prove2.me/theorems/cb72235a-4ca1-5ef1-9c44-a8a9c89e8665
-- title:
--   Local Lemma: measure Real avoid insert
-- statement:
--   The Local Lemma construction uses the measure Real avoid insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/lovasz-local-lemma/blob/9d020fa8fb20e9426c2d6780a3cfab4a68794d89/LocalLemmaLib/LocalLemma.lean#L61-L67
-- source:
--   https://github.com/jtraverso/lovasz-local-lemma/blob/9d020fa8fb20e9426c2d6780a3cfab4a68794d89/LocalLemmaLib/LocalLemma.lean#L61-L67

module
public import Mathlib
public import Definitions.Def_LocalLemmaLib_Coin
public import Definitions.Def_LocalLemmaLib_LocalLemma
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory
open LocalLemma

theorem LocalLemma.measureReal_avoid_insert {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] {n : ℕ} (A : Fin n → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (S : Finset (Fin n)) (j : Fin n) :
    μ.real (avoid A (insert j S)) = μ.real (avoid A S) - μ.real (avoid A S ∩ A j) := by sorry
