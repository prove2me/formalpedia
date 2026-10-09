-- Prove2me | Theorems.Thm_OAI_Snaky21_Certificate_final_calculations_part07_correct
-- name    : OAI.Snaky21.Certificate.final_calculations_part07_correct
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-09T08:49:30.191538+00:00
-- url     : https://prove2.me/theorems/f1266150-3198-4fe1-8ad8-8f91d5b3d132
-- title:
--   Final Snaky certificate: finite calculations 112–127
-- statement:
--   The fixed placements and finite-set operations in this batch equal their literal integer-grid outputs. These equalities supply the required sets, envelopes, and heights in the final 32-child certificate composition.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Snaky-in-21-Maker-moves-September-25-2026/article.pdf; Proposition 5 and the last certificate row (numbered card 727).

import Definitions.Def_Snaky21Calc11Part11
open OAI.Snaky21 OAI.SnakyPrototype OAI.Snaky21.Certificate

theorem OAI.Snaky21.Certificate.final_calculations_part07_correct : (calc11_card_2314.envelope ∩ calc11_set_2410 = calc11_set_2411) ∧ (calc11_card_2313.envelope ∩ calc11_set_2411 = calc11_set_2412) ∧ (calc11_card_2312.envelope ∩ calc11_set_2412 = calc11_set_2413) ∧ (calc11_card_2311.envelope ∩ calc11_set_2413 = calc11_set_2414) ∧ (calc11_card_2310.envelope ∩ calc11_set_2414 = calc11_set_2415) ∧ (calc11_card_2309.envelope ∩ calc11_set_2415 = calc11_set_2416) ∧ (calc11_card_2308.envelope ∩ calc11_set_2416 = calc11_set_2417) ∧ (calc11_card_2307.envelope ∩ calc11_set_2417 = calc11_set_2418) ∧ (calc11_card_2306.envelope ∩ calc11_set_2418 = calc11_set_2419) ∧ (calc11_card_2305.envelope ∩ calc11_set_2419 = calc11_set_2420) ∧ (calc11_card_2304.envelope ∩ calc11_set_2420 = calc11_set_2421) ∧ (calc11_card_2303.envelope ∩ calc11_set_2421 = calc11_set_2422) ∧ (calc11_card_2302.envelope ∩ calc11_set_2422 = calc11_set_2423) ∧ (calc11_card_2301.envelope ∩ calc11_set_2423 = calc11_set_2424) ∧ (calc11_card_2300.envelope ∩ calc11_set_2424 = calc11_set_2425) ∧ (calc11_set_2393 ∪ calc11_set_2425 = calc11_set_2426) ∧ True := by sorry
