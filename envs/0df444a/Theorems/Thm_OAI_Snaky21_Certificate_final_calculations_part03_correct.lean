-- Prove2me | Theorems.Thm_OAI_Snaky21_Certificate_final_calculations_part03_correct
-- name    : OAI.Snaky21.Certificate.final_calculations_part03_correct
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-09T08:38:49.928526+00:00
-- url     : https://prove2.me/theorems/a1a42b6d-0533-41ef-bc9c-27171dbc26e9
-- title:
--   Final Snaky certificate: finite calculations 48–63
-- statement:
--   The fixed placements and finite-set operations in this batch equal their literal integer-grid outputs. These equalities supply the required sets, envelopes, and heights in the final 32-child certificate composition.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Snaky-in-21-Maker-moves-September-25-2026/article.pdf; Proposition 5 and the last certificate row (numbered card 727).

import Definitions.Def_Snaky21Calc11Part11
open OAI.Snaky21 OAI.SnakyPrototype OAI.Snaky21.Certificate

theorem OAI.Snaky21.Certificate.final_calculations_part03_correct : (calc11_card_2322.required ∪ calc11_set_2345 = calc11_set_2347) ∧ (calc11_card_2322.envelope ∪ calc11_set_2346 = calc11_set_2348) ∧ (calc11_card_2321.required ∪ calc11_set_2347 = calc11_set_2349) ∧ (calc11_card_2321.envelope ∪ calc11_set_2348 = calc11_set_2350) ∧ (calc11_card_2320.required ∪ calc11_set_2349 = calc11_set_2351) ∧ (calc11_card_2320.envelope ∪ calc11_set_2350 = calc11_set_2352) ∧ (calc11_card_2319.required ∪ calc11_set_2351 = calc11_set_2353) ∧ (calc11_card_2319.envelope ∪ calc11_set_2352 = calc11_set_2354) ∧ (calc11_card_2318.required ∪ calc11_set_2353 = calc11_set_2355) ∧ (calc11_card_2318.envelope ∪ calc11_set_2354 = calc11_set_2356) ∧ (calc11_card_2317.required ∪ calc11_set_2355 = calc11_set_2357) ∧ (calc11_card_2317.envelope ∪ calc11_set_2356 = calc11_set_2358) ∧ (calc11_card_2316.required ∪ calc11_set_2357 = calc11_set_2359) ∧ (calc11_card_2316.envelope ∪ calc11_set_2358 = calc11_set_2360) ∧ (calc11_card_2315.required ∪ calc11_set_2359 = calc11_set_2361) ∧ (calc11_card_2315.envelope ∪ calc11_set_2360 = calc11_set_2362) ∧ True := by sorry
