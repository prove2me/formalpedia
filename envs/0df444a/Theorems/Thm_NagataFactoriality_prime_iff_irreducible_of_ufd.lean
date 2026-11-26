-- Prove2me | Theorems.Thm_NagataFactoriality_prime_iff_irreducible_of_ufd
-- name    : NagataFactoriality.prime_iff_irreducible_of_ufd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:49:22.145342+00:00
-- url     : https://prove2.me/theorems/eeb97a47-d577-4df6-a03b-cbcac80c0a96
-- title:
--   Nagata Factoriality: prime iff irreducible of ufd
-- statement:
--   The Nagata Factoriality construction uses the prime iff irreducible of ufd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Basic/UFD.lean#L24-L26
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Basic/UFD.lean#L24-L26

import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Definitions.Def_NagataFactoriality_Basic_Noetherian
import Definitions.Def_NagataFactoriality_Basic_UFD
set_option autoImplicit false
open NagataFactoriality

theorem NagataFactoriality.prime_iff_irreducible_of_ufd {α : Type*} [CommRing α] [IsDomain α]
    [UniqueFactorizationMonoid α] {p : α} : Prime p ↔ Irreducible p := by sorry
