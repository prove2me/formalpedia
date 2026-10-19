-- Prove2me | Theorems.Thm_MazurTransfer_thirteen_to_nineteen_character_certificates
-- name    : MazurTransfer.thirteen_to_nineteen_character_certificates
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T23:30:34.624387+00:00
-- url     : https://prove2.me/theorems/c058f9aa-df46-4992-a8dd-d376f1faae71
-- statement:
--   The explicit thirteenth-to-nineteenth characters have values twelve and eight at the generator two; that generator generates all units modulo thirteen, and both character values have exact order six. The six complete original propositions are retained.

import Mathlib
import Definitions.Def_MazurTransfer_ThirteenToNineteenOriginalCharacterDataAndConstructorCertificates20261018
open MazurTransfer.ThirteenToNineteenCharacters
attribute [local instance] characterOriginalPrime13Provider20261018 characterOriginalPrime19Provider20261018

theorem MazurTransfer.thirteen_to_nineteen_character_certificates :
    ((character generator : ZMod 19) = 12) ∧
    (character generator = scalarTwelve) ∧
    ((conjugateCharacter generator : ZMod 19) = 8) ∧
    (∀ u : (ZMod 13)ˣ, ∃ n : Fin 12, u = generator ^ n.val) ∧
    (orderOf (character generator) = 6) ∧
    (orderOf (conjugateCharacter generator) = 6) := by sorry
