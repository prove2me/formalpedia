-- Prove2me | Theorems.Thm_NagataFactoriality_dvd_of_localization_dvd
-- name    : NagataFactoriality.dvd_of_localization_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:01:04.494912+00:00
-- url     : https://prove2.me/theorems/facb2ca8-9947-473c-9ab7-581fc7d978b5
-- title:
--   Nagata Factoriality: dvd of localization dvd
-- statement:
--   The Nagata Factoriality construction uses the dvd of localization dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Lemmas.lean#L582-L589
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Lemmas.lean#L582-L589

import Definitions.Def_NagataFactoriality_Localization_Properties
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
import Definitions.Def_NagataFactoriality_Basic_UFD
import Definitions.Def_NagataFactoriality_Nagata_Lemmas
set_option autoImplicit false
open NagataFactoriality

theorem NagataFactoriality.dvd_of_localization_dvd {α : Type*} [CommRing α] [IsDomain α] {S : Submonoid α}
    (hS : ∀ s ∈ S, Prime s ∨ IsUnit s) {p a : α} (hp : Irreducible p) (havoid : Avoids S p)
    (hdiv : Localization.of (S := S) p ∣ Localization.of (S := S) a) : p ∣ a := by sorry
