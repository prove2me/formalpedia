-- Prove2me | Theorems.Thm_NagataFactoriality_dvd_of_localization_dvd_primeGenerated
-- name    : NagataFactoriality.dvd_of_localization_dvd_primeGenerated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:00:32.525511+00:00
-- url     : https://prove2.me/theorems/7e0f76cf-057f-55e4-8308-5a7a03991f2c
-- title:
--   Nagata Factoriality: dvd of localization dvd prime Generated
-- statement:
--   The Nagata Factoriality construction uses the dvd of localization dvd prime Generated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Lemmas.lean#L168-L175
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Lemmas.lean#L168-L175

import Definitions.Def_NagataFactoriality_Localization_Properties
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
import Definitions.Def_NagataFactoriality_Basic_UFD
import Definitions.Def_NagataFactoriality_Nagata_Lemmas
set_option autoImplicit false
open NagataFactoriality

theorem NagataFactoriality.dvd_of_localization_dvd_primeGenerated {α : Type*} [CommRing α] [IsDomain α]
    {S : Submonoid α} (hS : PrimeGenerated S) {p a : α} (hp : Irreducible p)
    (havoid : Avoids S p) (hdiv : Localization.of (S := S) p ∣ Localization.of (S := S) a) : p ∣ a := by sorry
