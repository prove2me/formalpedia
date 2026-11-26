-- Prove2me | Theorems.Thm_NagataFactoriality_primeGenerated_powers
-- name    : NagataFactoriality.primeGenerated_powers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:59:28.017894+00:00
-- url     : https://prove2.me/theorems/69c96e08-22b0-4ca6-a67c-a42e1787e549
-- title:
--   Nagata Factoriality: prime Generated powers
-- statement:
--   The Nagata Factoriality construction uses the prime Generated powers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Lemmas.lean#L37-L46
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Lemmas.lean#L37-L46

import Definitions.Def_NagataFactoriality_Localization_Properties
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
import Definitions.Def_NagataFactoriality_Basic_UFD
import Definitions.Def_NagataFactoriality_Nagata_Lemmas
set_option autoImplicit false
open NagataFactoriality

theorem NagataFactoriality.primeGenerated_powers {α : Type*} [CommRing α] {p : α} (hp : Prime p) :
    PrimeGenerated (Submonoid.powers p) := by sorry
