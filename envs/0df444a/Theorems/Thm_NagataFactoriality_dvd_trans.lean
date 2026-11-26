-- Prove2me | Theorems.Thm_NagataFactoriality_dvd_trans
-- name    : NagataFactoriality.dvd_trans
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:47:18.719799+00:00
-- url     : https://prove2.me/theorems/5d7f758c-f881-4abb-af00-16930dfe1e6b
-- title:
--   Nagata Factoriality: dvd trans
-- statement:
--   The Nagata Factoriality construction uses the dvd trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Basic/Divisibility.lean#L25-L28
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Basic/Divisibility.lean#L25-L28

import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
import Definitions.Def_NagataFactoriality_Basic_Ring
import Definitions.Def_NagataFactoriality_Basic_Divisibility
set_option autoImplicit false
open NagataFactoriality
open scoped BigOperators

theorem NagataFactoriality.dvd_trans {α : Type*} [CommMonoid α] {a b c : α} :
    a ∣ b → b ∣ c → a ∣ c := by sorry
