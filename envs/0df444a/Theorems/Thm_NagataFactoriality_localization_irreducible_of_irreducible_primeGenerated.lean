-- Prove2me | Theorems.Thm_NagataFactoriality_localization_irreducible_of_irreducible_primeGenerated
-- name    : NagataFactoriality.localization_irreducible_of_irreducible_primeGenerated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:00:44.122706+00:00
-- url     : https://prove2.me/theorems/6ea88856-d2c6-53a5-ac48-d114e54901b4
-- title:
--   Nagata Factoriality: localization irreducible of irreducible prime Generated
-- statement:
--   The Nagata Factoriality construction uses the localization irreducible of irreducible prime Generated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Lemmas.lean#L335-L342
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Lemmas.lean#L335-L342

import Definitions.Def_NagataFactoriality_Localization_Properties
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
import Definitions.Def_NagataFactoriality_Basic_UFD
import Definitions.Def_NagataFactoriality_Nagata_Lemmas
set_option autoImplicit false
open NagataFactoriality

theorem NagataFactoriality.localization_irreducible_of_irreducible_primeGenerated {α : Type*}
    [CommRing α] [IsDomain α] {S : Submonoid α} (hS : PrimeGenerated S) {p : α}
    (hp : Irreducible p) (havoid : Avoids S p) : Irreducible (Localization.of (S := S) p) := by sorry
