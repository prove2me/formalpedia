-- Prove2me | Theorems.Thm_NagataFactoriality_localization_irreducible_of_irreducible_primeGenerated_isLocalization
-- name    : NagataFactoriality.localization_irreducible_of_irreducible_primeGenerated_isLocalization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:58:33.925967+00:00
-- url     : https://prove2.me/theorems/a94e7996-9e69-4a53-aa09-ce1cb7352617
-- title:
--   Nagata Factoriality: localization irreducible of irreducible prime Generated is Localization
-- statement:
--   The Nagata Factoriality construction uses the localization irreducible of irreducible prime Generated is Localization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Lemmas.lean#L260-L333
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Lemmas.lean#L260-L333

import Definitions.Def_NagataFactoriality_Localization_Properties
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
import Definitions.Def_NagataFactoriality_Basic_UFD
import Definitions.Def_NagataFactoriality_Nagata_Lemmas
set_option autoImplicit false
open NagataFactoriality

theorem NagataFactoriality.localization_irreducible_of_irreducible_primeGenerated_isLocalization {α β : Type*}
    [CommRing α] [IsDomain α] {S : Submonoid α} [CommRing β] [Algebra α β] [IsDomain β]
    [_root_.IsLocalization S β] (hS : PrimeGenerated S) {p : α} (hp : Irreducible p)
    (havoid : Avoids S p) : Irreducible (algebraMap α β p) := by sorry
