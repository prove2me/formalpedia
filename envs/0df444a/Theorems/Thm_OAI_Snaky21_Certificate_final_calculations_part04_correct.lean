-- Prove2me | Theorems.Thm_OAI_Snaky21_Certificate_final_calculations_part04_correct
-- name    : OAI.Snaky21.Certificate.final_calculations_part04_correct
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-09T08:42:38.646265+00:00
-- url     : https://prove2.me/theorems/2cb8f3b0-a33e-405b-b022-530c678a2193
-- title:
--   Final Snaky certificate: finite calculations 64–79
-- statement:
--   The fixed placements and finite-set operations in this batch equal their literal integer-grid outputs. These equalities supply the required sets, envelopes, and heights in the final 32-child certificate composition.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Snaky-in-21-Maker-moves-September-25-2026/article.pdf; Proposition 5 and the last certificate row (numbered card 727).

import Definitions.Def_Snaky21Calc11Part11
open OAI.Snaky21 OAI.SnakyPrototype OAI.Snaky21.Certificate

theorem OAI.Snaky21.Certificate.final_calculations_part04_correct : (calc11_card_2314.required ∪ calc11_set_2361 = calc11_set_2363) ∧ (calc11_card_2314.envelope ∪ calc11_set_2362 = calc11_set_2364) ∧ (calc11_card_2313.required ∪ calc11_set_2363 = calc11_set_2365) ∧ (calc11_card_2313.envelope ∪ calc11_set_2364 = calc11_set_2366) ∧ (calc11_card_2312.required ∪ calc11_set_2365 = calc11_set_2367) ∧ (calc11_card_2312.envelope ∪ calc11_set_2366 = calc11_set_2368) ∧ (calc11_card_2311.required ∪ calc11_set_2367 = calc11_set_2369) ∧ (calc11_card_2311.envelope ∪ calc11_set_2368 = calc11_set_2370) ∧ (calc11_card_2310.required ∪ calc11_set_2369 = calc11_set_2371) ∧ (calc11_card_2310.envelope ∪ calc11_set_2370 = calc11_set_2372) ∧ (calc11_card_2309.required ∪ calc11_set_2371 = calc11_set_2373) ∧ (calc11_card_2309.envelope ∪ calc11_set_2372 = calc11_set_2374) ∧ (calc11_card_2308.required ∪ calc11_set_2373 = calc11_set_2375) ∧ (calc11_card_2308.envelope ∪ calc11_set_2374 = calc11_set_2376) ∧ (calc11_card_2307.required ∪ calc11_set_2375 = calc11_set_2377) ∧ (calc11_card_2307.envelope ∪ calc11_set_2376 = calc11_set_2378) ∧ True := by sorry
