-- Prove2me | Theorems.Thm_NagataFactoriality_prime_of_irreducible_of_dvd_mem
-- name    : NagataFactoriality.prime_of_irreducible_of_dvd_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:59:57.115483+00:00
-- url     : https://prove2.me/theorems/7c24c970-6226-4da1-bb6a-e8ce96a68145
-- title:
--   Nagata Factoriality: prime of irreducible of dvd mem
-- statement:
--   The Nagata Factoriality construction uses the prime of irreducible of dvd mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Lemmas.lean#L406-L413
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Lemmas.lean#L406-L413

import Definitions.Def_NagataFactoriality_Localization_Properties
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
import Definitions.Def_NagataFactoriality_Basic_UFD
import Definitions.Def_NagataFactoriality_Nagata_Lemmas
set_option autoImplicit false
open NagataFactoriality

theorem NagataFactoriality.prime_of_irreducible_of_dvd_mem {α : Type*} [CommRing α] [IsDomain α] {S : Submonoid α}
    (hS : ∀ s ∈ S, Prime s ∨ IsUnit s) {p s : α}
    (hp : Irreducible p) (hs : s ∈ S) (hdiv : p ∣ s) : Prime p := by sorry
