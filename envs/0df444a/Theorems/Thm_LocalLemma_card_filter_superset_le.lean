-- Prove2me | Theorems.Thm_LocalLemma_card_filter_superset_le
-- name    : LocalLemma.card_filter_superset_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:21:32.174609+00:00
-- url     : https://prove2.me/theorems/e1308939-b820-4e9c-8922-6d3fab82c609
-- title:
--   Local Lemma: card filter superset le
-- statement:
--   Number of `k`-subsets of `Fin n` containing a fixed pair.
--
--   Source: https://github.com/jtraverso/lovasz-local-lemma/blob/9d020fa8fb20e9426c2d6780a3cfab4a68794d89/LocalLemmaLib/LocalLemma.lean#L250-L267
-- source:
--   https://github.com/jtraverso/lovasz-local-lemma/blob/9d020fa8fb20e9426c2d6780a3cfab4a68794d89/LocalLemmaLib/LocalLemma.lean#L250-L267

module
public import Mathlib
public import Definitions.Def_LocalLemmaLib_Coin
public import Definitions.Def_LocalLemmaLib_LocalLemma
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory
open LocalLemma

theorem LocalLemma.card_filter_superset_le {n k : ℕ} (e : Finset (Fin n)) (he : e.card = 2) :
    (((Finset.univ : Finset (Fin n)).powersetCard k).filter (e ⊆ ·)).card ≤
      n.choose (k - 2) := by sorry
