-- Prove2me | Theorems.Thm_NagataFactoriality_prime_of_localization_prime_primeGenerated
-- name    : NagataFactoriality.prime_of_localization_prime_primeGenerated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:00:44.9028+00:00
-- url     : https://prove2.me/theorems/df695864-6195-535f-84e7-1d5c4d9651c8
-- title:
--   Nagata Factoriality: prime of localization prime prime Generated
-- statement:
--   The Nagata Factoriality construction uses the prime of localization prime prime Generated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Lemmas.lean#L363-L370
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Lemmas.lean#L363-L370

import Definitions.Def_NagataFactoriality_Localization_Properties
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
import Definitions.Def_NagataFactoriality_Basic_UFD
import Definitions.Def_NagataFactoriality_Nagata_Lemmas
set_option autoImplicit false
open NagataFactoriality

theorem NagataFactoriality.prime_of_localization_prime_primeGenerated {α : Type*} [CommRing α] [IsDomain α]
    {S : Submonoid α} (hS : PrimeGenerated S) {p : α} (hp : Irreducible p)
    (havoid : Avoids S p) (hploc : Prime (Localization.of (S := S) p)) : Prime p := by sorry
