-- Prove2me | Theorems.Thm_NagataFactoriality_nagata_key_lemma_primeGenerated_isLocalization
-- name    : NagataFactoriality.nagata_key_lemma_primeGenerated_isLocalization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:58:13.729517+00:00
-- url     : https://prove2.me/theorems/61c441f7-bf46-537f-97d7-0077d5166df0
-- title:
--   Nagata Factoriality: nagata key lemma prime Generated is Localization
-- statement:
--   The Nagata Factoriality construction uses the nagata key lemma prime Generated is Localization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Lemmas.lean#L372-L389
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Lemmas.lean#L372-L389

import Definitions.Def_NagataFactoriality_Localization_Properties
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
import Definitions.Def_NagataFactoriality_Basic_UFD
import Definitions.Def_NagataFactoriality_Nagata_Lemmas
set_option autoImplicit false
open NagataFactoriality

theorem NagataFactoriality.nagata_key_lemma_primeGenerated_isLocalization {α β : Type*}
    [CommRing α] [IsDomain α] {S : Submonoid α} [CommRing β] [Algebra α β] [IsDomain β]
    [_root_.IsLocalization S β] (hS : PrimeGenerated S) [UniqueFactorizationMonoid β]
    {p : α} (hp : Irreducible p) : Prime p := by sorry
