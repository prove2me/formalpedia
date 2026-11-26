-- Prove2me | Theorems.Thm_NagataFactoriality_primeGenerated_closure_of_primes
-- name    : NagataFactoriality.primeGenerated_closure_of_primes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:58:18.417883+00:00
-- url     : https://prove2.me/theorems/81e16355-6be4-5289-9c15-2a2561c152d1
-- title:
--   Nagata Factoriality: prime Generated closure of primes
-- statement:
--   The Nagata Factoriality construction uses the prime Generated closure of primes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Lemmas.lean#L48-L67
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Lemmas.lean#L48-L67

import Definitions.Def_NagataFactoriality_Localization_Properties
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
import Definitions.Def_NagataFactoriality_Basic_UFD
import Definitions.Def_NagataFactoriality_Nagata_Lemmas
set_option autoImplicit false
open NagataFactoriality

theorem NagataFactoriality.primeGenerated_closure_of_primes {α : Type*} [CommRing α] {s : Set α}
    (hs : ∀ q ∈ s, Prime q) : PrimeGenerated (Submonoid.closure s) := by sorry
