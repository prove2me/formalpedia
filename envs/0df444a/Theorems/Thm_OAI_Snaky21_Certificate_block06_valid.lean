-- Prove2me | Theorems.Thm_OAI_Snaky21_Certificate_block06_valid
-- name    : OAI.Snaky21.Certificate.block06_valid
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-08T10:49:50.006148+00:00
-- url     : https://prove2.me/theorems/f31e35e5-8e91-423b-9557-501fbc4d82ec
-- title:
--   21-move certificate: validity of numbered cards 384–447
-- statement:
--   Every numbered card from 384 through 447 of the fixed 21-move certificate is a valid conditional claim. The required set, envelope and height are the literal finite reconstruction of the printed data, including every nested combination. Every actual combination equation is checked by Lean kernel reduction, and the game meaning follows from the conditional-claim calculus and earlier numbered cards.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Snaky-in-21-Maker-moves-September-25-2026/article.pdf; Proposition 5, 21-move certificate appendix, numbered cards 384–447.

import Definitions.Def_Snaky21Data06
import Theorems.Thm_OAI_Snaky21_claim_calculus
import Theorems.Thm_OAI_Snaky21_Certificate_block05_valid
open OAI.Snaky21 OAI.SnakyPrototype OAI.Snaky21.Certificate

theorem OAI.Snaky21.Certificate.block06_valid : Valid card_384 ∧ Valid card_385 ∧ Valid card_386 ∧ Valid card_387 ∧ Valid card_388 ∧ Valid card_389 ∧ Valid card_390 ∧ Valid card_391 ∧ Valid card_392 ∧ Valid card_393 ∧ Valid card_394 ∧ Valid card_395 ∧ Valid card_396 ∧ Valid card_397 ∧ Valid card_398 ∧ Valid card_399 ∧ Valid card_400 ∧ Valid card_401 ∧ Valid card_402 ∧ Valid card_403 ∧ Valid card_404 ∧ Valid card_405 ∧ Valid card_406 ∧ Valid card_407 ∧ Valid card_408 ∧ Valid card_409 ∧ Valid card_410 ∧ Valid card_411 ∧ Valid card_412 ∧ Valid card_413 ∧ Valid card_414 ∧ Valid card_415 ∧ Valid card_416 ∧ Valid card_417 ∧ Valid card_418 ∧ Valid card_419 ∧ Valid card_420 ∧ Valid card_421 ∧ Valid card_422 ∧ Valid card_423 ∧ Valid card_424 ∧ Valid card_425 ∧ Valid card_426 ∧ Valid card_427 ∧ Valid card_428 ∧ Valid card_429 ∧ Valid card_430 ∧ Valid card_431 ∧ Valid card_432 ∧ Valid card_433 ∧ Valid card_434 ∧ Valid card_435 ∧ Valid card_436 ∧ Valid card_437 ∧ Valid card_438 ∧ Valid card_439 ∧ Valid card_440 ∧ Valid card_441 ∧ Valid card_442 ∧ Valid card_443 ∧ Valid card_444 ∧ Valid card_445 ∧ Valid card_446 ∧ Valid card_447 ∧ True := by sorry
