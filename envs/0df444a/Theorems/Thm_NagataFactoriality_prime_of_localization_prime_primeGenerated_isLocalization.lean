-- Prove2me | Theorems.Thm_NagataFactoriality_prime_of_localization_prime_primeGenerated_isLocalization
-- name    : NagataFactoriality.prime_of_localization_prime_primeGenerated_isLocalization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:58:43.014805+00:00
-- url     : https://prove2.me/theorems/9dfe5008-a006-460e-a8fa-40d5fb128d91
-- title:
--   Nagata Factoriality: prime of localization prime prime Generated is Localization
-- statement:
--   The Nagata Factoriality construction uses the prime of localization prime prime Generated is Localization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Lemmas.lean#L344-L361
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Lemmas.lean#L344-L361

import Definitions.Def_NagataFactoriality_Localization_Properties
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
import Definitions.Def_NagataFactoriality_Basic_UFD
import Definitions.Def_NagataFactoriality_Nagata_Lemmas
set_option autoImplicit false
open NagataFactoriality

theorem NagataFactoriality.prime_of_localization_prime_primeGenerated_isLocalization {α β : Type*}
    [CommRing α] [IsDomain α] {S : Submonoid α} [CommRing β] [Algebra α β] [IsDomain β]
    [_root_.IsLocalization S β] (hS : PrimeGenerated S) {p : α} (hp : Irreducible p)
    (havoid : Avoids S p) (hploc : Prime (algebraMap α β p)) : Prime p := by sorry
