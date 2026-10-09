-- Prove2me | Theorems.Thm_OAI_Snaky21_certificate21_correct
-- name    : OAI.Snaky21.certificate21_correct
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-09T08:56:44.904009+00:00
-- url     : https://prove2.me/theorems/ba695ae1-f3b2-424c-8455-8c7d91c7e666
-- title:
--   Proposition 5 — the valid empty-requirement card of height 21
-- statement:
--   The final numbered card 727 of the fixed 21-move certificate is a valid conditional Snaky claim, its required Maker set is empty, its height is 21, and its finite envelope has exactly 251 cells, all with both coordinates between 0 and 16. The validity is obtained from all numbered cards and their nested combinations, rather than assumed from the finite reconstruction alone.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Snaky-in-21-Maker-moves-September-25-2026/article.pdf; Proposition 5, endpoint of the 21-move certificate; Lemmas 3 and 4 supply semantic validity.

import Definitions.Def_Snaky21Catalog
import Definitions.Def_Snaky21Data11
open OAI.Snaky21 OAI.SnakyPrototype OAI.Snaky21.Certificate

theorem OAI.Snaky21.certificate21_correct : Valid card_727 ∧ (card_727.required = ∅ ∧ card_727.height = 21 ∧ card_727.envelope.card = 251 ∧ (∀ x ∈ card_727.envelope, 0 ≤ x.1 ∧ x.1 ≤ 16 ∧ 0 ≤ x.2 ∧ x.2 ≤ 16)) ∧ (numberedCards.length = 728 ∧ (numberedCards.map (fun c => decide (0 < c.height ∧ c.height ≤ 21))).all id = true) := by sorry
