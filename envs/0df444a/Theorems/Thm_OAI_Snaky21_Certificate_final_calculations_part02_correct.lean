-- Prove2me | Theorems.Thm_OAI_Snaky21_Certificate_final_calculations_part02_correct
-- name    : OAI.Snaky21.Certificate.final_calculations_part02_correct
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-09T08:38:20.805074+00:00
-- url     : https://prove2.me/theorems/8fb47715-7081-4516-a107-83789ad42d41
-- title:
--   Final Snaky certificate: finite calculations 32–47
-- statement:
--   The fixed placements and finite-set operations in this batch equal their literal integer-grid outputs. These equalities supply the required sets, envelopes, and heights in the final 32-child certificate composition.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Snaky-in-21-Maker-moves-September-25-2026/article.pdf; Proposition 5 and the last certificate row (numbered card 727).

import Definitions.Def_Snaky21Calc11Part11
open OAI.Snaky21 OAI.SnakyPrototype OAI.Snaky21.Certificate

theorem OAI.Snaky21.Certificate.final_calculations_part02_correct : (calc11_card_2330.required ∪ ∅ = calc11_set_2331) ∧ (calc11_card_2330.envelope ∪ ∅ = calc11_set_2332) ∧ (calc11_card_2329.required ∪ calc11_set_2331 = calc11_set_2333) ∧ (calc11_card_2329.envelope ∪ calc11_set_2332 = calc11_set_2334) ∧ (calc11_card_2328.required ∪ calc11_set_2333 = calc11_set_2335) ∧ (calc11_card_2328.envelope ∪ calc11_set_2334 = calc11_set_2336) ∧ (calc11_card_2327.required ∪ calc11_set_2335 = calc11_set_2337) ∧ (calc11_card_2327.envelope ∪ calc11_set_2336 = calc11_set_2338) ∧ (calc11_card_2326.required ∪ calc11_set_2337 = calc11_set_2339) ∧ (calc11_card_2326.envelope ∪ calc11_set_2338 = calc11_set_2340) ∧ (calc11_card_2325.required ∪ calc11_set_2339 = calc11_set_2341) ∧ (calc11_card_2325.envelope ∪ calc11_set_2340 = calc11_set_2342) ∧ (calc11_card_2324.required ∪ calc11_set_2341 = calc11_set_2343) ∧ (calc11_card_2324.envelope ∪ calc11_set_2342 = calc11_set_2344) ∧ (calc11_card_2323.required ∪ calc11_set_2343 = calc11_set_2345) ∧ (calc11_card_2323.envelope ∪ calc11_set_2344 = calc11_set_2346) ∧ True := by sorry
