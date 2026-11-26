-- Prove2me | Theorems.Thm_NagataFactoriality_prime_irreducible
-- name    : NagataFactoriality.prime_irreducible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:47:20.208054+00:00
-- url     : https://prove2.me/theorems/26cc0667-edef-4528-9bac-d4b7a2d37014
-- title:
--   Nagata Factoriality: prime irreducible
-- statement:
--   The Nagata Factoriality construction uses the prime irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Basic/Divisibility.lean#L65-L67
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Basic/Divisibility.lean#L65-L67

import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
import Definitions.Def_NagataFactoriality_Basic_Ring
import Definitions.Def_NagataFactoriality_Basic_Divisibility
set_option autoImplicit false
open NagataFactoriality
open scoped BigOperators

theorem NagataFactoriality.prime_irreducible {α : Type*} [CommRing α] [IsDomain α] {p : α} (hp : Prime p) :
    Irreducible p := by sorry
