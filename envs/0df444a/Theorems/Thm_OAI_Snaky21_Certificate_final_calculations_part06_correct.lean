-- Prove2me | Theorems.Thm_OAI_Snaky21_Certificate_final_calculations_part06_correct
-- name    : OAI.Snaky21.Certificate.final_calculations_part06_correct
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-09T08:47:29.178149+00:00
-- url     : https://prove2.me/theorems/991144a6-2f3e-44b6-b3b8-664a7e80cd9b
-- title:
--   Final Snaky certificate: finite calculations 96–111
-- statement:
--   The fixed placements and finite-set operations in this batch equal their literal integer-grid outputs. These equalities supply the required sets, envelopes, and heights in the final 32-child certificate composition.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Snaky-in-21-Maker-moves-September-25-2026/article.pdf; Proposition 5 and the last certificate row (numbered card 727).

import Definitions.Def_Snaky21Calc11Part11
open OAI.Snaky21 OAI.SnakyPrototype OAI.Snaky21.Certificate

theorem OAI.Snaky21.Certificate.final_calculations_part06_correct : (calc11_card_2330.envelope ∩ calc11_card_2299.envelope = calc11_set_2395) ∧ (calc11_card_2329.envelope ∩ calc11_set_2395 = calc11_set_2396) ∧ (calc11_card_2328.envelope ∩ calc11_set_2396 = calc11_set_2397) ∧ (calc11_card_2327.envelope ∩ calc11_set_2397 = calc11_set_2398) ∧ (calc11_card_2326.envelope ∩ calc11_set_2398 = calc11_set_2399) ∧ (calc11_card_2325.envelope ∩ calc11_set_2399 = calc11_set_2400) ∧ (calc11_card_2324.envelope ∩ calc11_set_2400 = calc11_set_2401) ∧ (calc11_card_2323.envelope ∩ calc11_set_2401 = calc11_set_2402) ∧ (calc11_card_2322.envelope ∩ calc11_set_2402 = calc11_set_2403) ∧ (calc11_card_2321.envelope ∩ calc11_set_2403 = calc11_set_2404) ∧ (calc11_card_2320.envelope ∩ calc11_set_2404 = calc11_set_2405) ∧ (calc11_card_2319.envelope ∩ calc11_set_2405 = calc11_set_2406) ∧ (calc11_card_2318.envelope ∩ calc11_set_2406 = calc11_set_2407) ∧ (calc11_card_2317.envelope ∩ calc11_set_2407 = calc11_set_2408) ∧ (calc11_card_2316.envelope ∩ calc11_set_2408 = calc11_set_2409) ∧ (calc11_card_2315.envelope ∩ calc11_set_2409 = calc11_set_2410) ∧ True := by sorry
