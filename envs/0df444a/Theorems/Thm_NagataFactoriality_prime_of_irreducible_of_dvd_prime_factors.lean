-- Prove2me | Theorems.Thm_NagataFactoriality_prime_of_irreducible_of_dvd_prime_factors
-- name    : NagataFactoriality.prime_of_irreducible_of_dvd_prime_factors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:59:47.874798+00:00
-- url     : https://prove2.me/theorems/3b8c50c9-16d8-4510-b306-d2714fd0b080
-- title:
--   Nagata Factoriality: prime of irreducible of dvd prime factors
-- statement:
--   The Nagata Factoriality construction uses the prime of irreducible of dvd prime factors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Lemmas.lean#L73-L100
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Lemmas.lean#L73-L100

import Definitions.Def_NagataFactoriality_Localization_Properties
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
import Definitions.Def_NagataFactoriality_Basic_UFD
import Definitions.Def_NagataFactoriality_Nagata_Lemmas
set_option autoImplicit false
open NagataFactoriality

theorem NagataFactoriality.prime_of_irreducible_of_dvd_prime_factors {α : Type*} [CommRing α] [IsDomain α]
    {f : Multiset α} (hf : ∀ q ∈ f, Prime q) {p : α}
    (hp : Irreducible p) (hdiv : p ∣ f.prod) : Prime p := by sorry
