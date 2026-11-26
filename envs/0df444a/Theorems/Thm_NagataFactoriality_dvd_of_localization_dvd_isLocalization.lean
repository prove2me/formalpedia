-- Prove2me | Theorems.Thm_NagataFactoriality_dvd_of_localization_dvd_isLocalization
-- name    : NagataFactoriality.dvd_of_localization_dvd_isLocalization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:59:02.36329+00:00
-- url     : https://prove2.me/theorems/ae534aa8-ddcf-4d66-a999-b46732a1d05a
-- title:
--   Nagata Factoriality: dvd of localization dvd is Localization
-- statement:
--   The Nagata Factoriality construction uses the dvd of localization dvd is Localization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Lemmas.lean#L551-L580
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Lemmas.lean#L551-L580

import Definitions.Def_NagataFactoriality_Localization_Properties
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
import Definitions.Def_NagataFactoriality_Basic_UFD
import Definitions.Def_NagataFactoriality_Nagata_Lemmas
set_option autoImplicit false
open NagataFactoriality

theorem NagataFactoriality.dvd_of_localization_dvd_isLocalization {α β : Type*}
    [CommRing α] [IsDomain α] {S : Submonoid α} [CommRing β] [Algebra α β] [IsDomain β]
    [_root_.IsLocalization S β] (hS : ∀ s ∈ S, Prime s ∨ IsUnit s) {p a : α}
    (hp : Irreducible p) (havoid : Avoids S p) (hdiv : algebraMap α β p ∣ algebraMap α β a) :
    p ∣ a := by sorry
