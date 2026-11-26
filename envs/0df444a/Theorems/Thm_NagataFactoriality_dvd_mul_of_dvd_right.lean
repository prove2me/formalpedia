-- Prove2me | Theorems.Thm_NagataFactoriality_dvd_mul_of_dvd_right
-- name    : NagataFactoriality.dvd_mul_of_dvd_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:49:04.263798+00:00
-- url     : https://prove2.me/theorems/8a234dc0-dc6b-5261-9d75-38cc98e59b3f
-- title:
--   Nagata Factoriality: dvd mul of dvd right
-- statement:
--   The Nagata Factoriality construction uses the dvd mul of dvd right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Basic/Divisibility.lean#L35-L38
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Basic/Divisibility.lean#L35-L38

import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
import Definitions.Def_NagataFactoriality_Basic_Ring
import Definitions.Def_NagataFactoriality_Basic_Divisibility
set_option autoImplicit false
open NagataFactoriality
open scoped BigOperators

theorem NagataFactoriality.dvd_mul_of_dvd_right {α : Type*} [CommMonoid α] {a b c : α} :
    a ∣ c → a ∣ b * c := by sorry
