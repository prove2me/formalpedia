-- Prove2me | Theorems.Thm_OAI_Snaky21_Certificate_final_calculations_part05_correct
-- name    : OAI.Snaky21.Certificate.final_calculations_part05_correct
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-09T08:48:11.525725+00:00
-- url     : https://prove2.me/theorems/517071e9-5f1c-4bca-8b44-36e6d7750370
-- title:
--   Final Snaky certificate: finite calculations 80–95
-- statement:
--   The fixed placements and finite-set operations in this batch equal their literal integer-grid outputs. These equalities supply the required sets, envelopes, and heights in the final 32-child certificate composition.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Snaky-in-21-Maker-moves-September-25-2026/article.pdf; Proposition 5 and the last certificate row (numbered card 727).

import Definitions.Def_Snaky21Calc11Part11
open OAI.Snaky21 OAI.SnakyPrototype OAI.Snaky21.Certificate

theorem OAI.Snaky21.Certificate.final_calculations_part05_correct : (calc11_card_2306.required ∪ calc11_set_2377 = calc11_set_2379) ∧ (calc11_card_2306.envelope ∪ calc11_set_2378 = calc11_set_2380) ∧ (calc11_card_2305.required ∪ calc11_set_2379 = calc11_set_2381) ∧ (calc11_card_2305.envelope ∪ calc11_set_2380 = calc11_set_2382) ∧ (calc11_card_2304.required ∪ calc11_set_2381 = calc11_set_2383) ∧ (calc11_card_2304.envelope ∪ calc11_set_2382 = calc11_set_2384) ∧ (calc11_card_2303.required ∪ calc11_set_2383 = calc11_set_2385) ∧ (calc11_card_2303.envelope ∪ calc11_set_2384 = calc11_set_2386) ∧ (calc11_card_2302.required ∪ calc11_set_2385 = calc11_set_2387) ∧ (calc11_card_2302.envelope ∪ calc11_set_2386 = calc11_set_2388) ∧ (calc11_card_2301.required ∪ calc11_set_2387 = calc11_set_2389) ∧ (calc11_card_2301.envelope ∪ calc11_set_2388 = calc11_set_2390) ∧ (calc11_card_2300.required ∪ calc11_set_2389 = calc11_set_2391) ∧ (calc11_card_2300.envelope ∪ calc11_set_2390 = calc11_set_2392) ∧ (calc11_card_2299.required ∪ calc11_set_2391 = calc11_set_2393) ∧ (calc11_card_2299.envelope ∪ calc11_set_2392 = calc11_set_2394) ∧ True := by sorry
