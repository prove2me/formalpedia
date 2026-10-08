-- Prove2me | Theorems.Thm_OAI_Snaky21_combination_rule
-- name    : OAI.Snaky21.combination_rule
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-08T07:40:03.512727+00:00
-- url     : https://prove2.me/theorems/ce9987f7-60c8-4eb2-80da-5e92fdb33aca
-- title:
--   Lemma 3 — sound combination of conditional Snaky claims
-- statement:
--   Let a finite nonempty list of conditional claims be valid for the Snaky game on the integer grid. Each claim specifies required Maker cells, a finite envelope avoiding Breaker, and a positive bound on further actual Maker claims. For any pivot p, form the parent envelope by adjoining p to the union of the child envelopes, and form the required set by deleting p from the union of all child required sets and the intersection of their envelopes. The parent is a valid conditional claim with height one plus the maximum child height. This remains true for arbitrary additional Maker ownership and Breaker cells outside the envelope.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Snaky-in-21-Maker-moves-September-25-2026/article.pdf; Lemma 3, Maker-turn assertion.

import Definitions.Def_Snaky21Core
open OAI.Snaky21 OAI.SnakyPrototype

theorem OAI.Snaky21.combination_rule (p : Cell) (cs : List Card) (hne : cs ≠ []) (hv : ∀ c ∈ cs, Valid c) : Valid (combine p cs) := by sorry
