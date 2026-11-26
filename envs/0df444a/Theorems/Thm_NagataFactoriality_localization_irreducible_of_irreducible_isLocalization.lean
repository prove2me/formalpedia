-- Prove2me | Theorems.Thm_NagataFactoriality_localization_irreducible_of_irreducible_isLocalization
-- name    : NagataFactoriality.localization_irreducible_of_irreducible_isLocalization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:58:43.557477+00:00
-- url     : https://prove2.me/theorems/72c08534-df8b-4f29-a0f0-8da1e902d378
-- title:
--   Nagata Factoriality: localization irreducible of irreducible is Localization
-- statement:
--   The Nagata Factoriality construction uses the localization irreducible of irreducible is Localization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Lemmas.lean#L415-L540
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Lemmas.lean#L415-L540

import Definitions.Def_NagataFactoriality_Localization_Properties
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
import Definitions.Def_NagataFactoriality_Basic_UFD
import Definitions.Def_NagataFactoriality_Nagata_Lemmas
set_option autoImplicit false
open NagataFactoriality

theorem NagataFactoriality.localization_irreducible_of_irreducible_isLocalization {α β : Type*}
    [CommRing α] [IsDomain α] {S : Submonoid α} [CommRing β] [Algebra α β] [IsDomain β]
    [_root_.IsLocalization S β] (hS : ∀ s ∈ S, Prime s ∨ IsUnit s) {p : α}
    (hp : Irreducible p) (havoid : Avoids S p) : Irreducible (algebraMap α β p) := by sorry
