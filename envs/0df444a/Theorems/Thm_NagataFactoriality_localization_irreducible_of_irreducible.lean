-- Prove2me | Theorems.Thm_NagataFactoriality_localization_irreducible_of_irreducible
-- name    : NagataFactoriality.localization_irreducible_of_irreducible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:01:12.881078+00:00
-- url     : https://prove2.me/theorems/219c708e-4d13-46c2-a912-1b5c33653abe
-- title:
--   Nagata Factoriality: localization irreducible of irreducible
-- statement:
--   The Nagata Factoriality construction uses the localization irreducible of irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Lemmas.lean#L542-L549
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Lemmas.lean#L542-L549

import Definitions.Def_NagataFactoriality_Localization_Properties
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
import Definitions.Def_NagataFactoriality_Basic_UFD
import Definitions.Def_NagataFactoriality_Nagata_Lemmas
set_option autoImplicit false
open NagataFactoriality

theorem NagataFactoriality.localization_irreducible_of_irreducible {α : Type*} [CommRing α] [IsDomain α]
    {S : Submonoid α} (hS : ∀ s ∈ S, Prime s ∨ IsUnit s) {p : α} (hp : Irreducible p)
    (havoid : Avoids S p) : Irreducible (Localization.of (S := S) p) := by sorry
