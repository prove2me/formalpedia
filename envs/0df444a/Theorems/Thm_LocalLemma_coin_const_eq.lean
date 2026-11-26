-- Prove2me | Theorems.Thm_LocalLemma_coin_const_eq
-- name    : LocalLemma.coin_const_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:20:30.797775+00:00
-- url     : https://prove2.me/theorems/d7026b60-2cae-4d01-b272-240893ab1e96
-- title:
--   Local Lemma: coin const eq
-- statement:
--   The Local Lemma construction uses the coin const eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/lovasz-local-lemma/blob/9d020fa8fb20e9426c2d6780a3cfab4a68794d89/LocalLemmaLib/Coin.lean#L82-L99
-- source:
--   https://github.com/jtraverso/lovasz-local-lemma/blob/9d020fa8fb20e9426c2d6780a3cfab4a68794d89/LocalLemmaLib/Coin.lean#L82-L99

module
public import Mathlib
public import Definitions.Def_LocalLemmaLib_Coin
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory
open LocalLemma

theorem LocalLemma.coin_const_eq {ι : Type*} [Fintype ι] (E : Finset ι) (b : Bool) :
    coinMeasure ι {ω | ∀ i ∈ E, ω i = b} = (2⁻¹ : ENNReal) ^ E.card := by sorry
