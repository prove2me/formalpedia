-- Prove2me | Theorems.Thm_NagataFactoriality_prime_of_localization_prime
-- name    : NagataFactoriality.prime_of_localization_prime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:01:13.456674+00:00
-- url     : https://prove2.me/theorems/7b216155-e5da-5075-87d9-becd9a854838
-- title:
--   Nagata Factoriality: prime of localization prime
-- statement:
--   The Nagata Factoriality construction uses the prime of localization prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Lemmas.lean#L608-L615
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Lemmas.lean#L608-L615

import Definitions.Def_NagataFactoriality_Localization_Properties
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
import Definitions.Def_NagataFactoriality_Basic_UFD
import Definitions.Def_NagataFactoriality_Nagata_Lemmas
set_option autoImplicit false
open NagataFactoriality

theorem NagataFactoriality.prime_of_localization_prime {α : Type*} [CommRing α] [IsDomain α] {S : Submonoid α}
    (hS : ∀ s ∈ S, Prime s ∨ IsUnit s) {p : α} (hp : Irreducible p) (havoid : Avoids S p)
    (hploc : Prime (Localization.of (S := S) p)) : Prime p := by sorry
