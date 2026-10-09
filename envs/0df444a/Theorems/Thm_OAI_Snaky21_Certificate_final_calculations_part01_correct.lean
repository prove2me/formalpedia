-- Prove2me | Theorems.Thm_OAI_Snaky21_Certificate_final_calculations_part01_correct
-- name    : OAI.Snaky21.Certificate.final_calculations_part01_correct
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-09T08:33:41.85893+00:00
-- url     : https://prove2.me/theorems/06504266-c6a7-45e7-8833-c89650c066fa
-- title:
--   Final Snaky certificate: finite calculations 16–31
-- statement:
--   The fixed placements and finite-set operations in this batch equal their literal integer-grid outputs. These equalities supply the required sets, envelopes, and heights in the final 32-child certificate composition.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Snaky-in-21-Maker-moves-September-25-2026/article.pdf; Proposition 5 and the last certificate row (numbered card 727).

import Definitions.Def_Snaky21Calc11Part11
open OAI.Snaky21 OAI.SnakyPrototype OAI.Snaky21.Certificate

theorem OAI.Snaky21.Certificate.final_calculations_part01_correct : (placed 4 (13, 3) card_713 = calc11_card_2315) ∧ (placed 5 (3, 13) card_713 = calc11_card_2316) ∧ (placed 2 (3, 13) card_713 = calc11_card_2317) ∧ (placed 3 (13, 3) card_713 = calc11_card_2318) ∧ (placed 0 (1, 1) card_725 = calc11_card_2319) ∧ (placed 1 (1, 1) card_725 = calc11_card_2320) ∧ (placed 4 (15, 1) card_725 = calc11_card_2321) ∧ (placed 5 (1, 15) card_725 = calc11_card_2322) ∧ (placed 2 (1, 15) card_725 = calc11_card_2323) ∧ (placed 3 (15, 1) card_725 = calc11_card_2324) ∧ (placed 6 (15, 15) card_725 = calc11_card_2325) ∧ (placed 7 (15, 15) card_725 = calc11_card_2326) ∧ (placed 1 (1, 1) card_726 = calc11_card_2327) ∧ (placed 4 (15, 1) card_726 = calc11_card_2328) ∧ (placed 2 (1, 15) card_726 = calc11_card_2329) ∧ (placed 6 (15, 15) card_726 = calc11_card_2330) ∧ True := by sorry
