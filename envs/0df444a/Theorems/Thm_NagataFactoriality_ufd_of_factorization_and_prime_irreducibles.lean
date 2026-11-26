-- Prove2me | Theorems.Thm_NagataFactoriality_ufd_of_factorization_and_prime_irreducibles
-- name    : NagataFactoriality.ufd_of_factorization_and_prime_irreducibles
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:01:44.509815+00:00
-- url     : https://prove2.me/theorems/9e13d34b-71f4-55f2-bf6d-bcb0038a60c2
-- title:
--   Nagata Factoriality: ufd of factorization and prime irreducibles
-- statement:
--   The Nagata Factoriality construction uses the ufd of factorization and prime irreducibles property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Theorem.lean#L94-L98
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Theorem.lean#L94-L98

import Definitions.Def_NagataFactoriality_Nagata_Lemmas
import Definitions.Def_NagataFactoriality_Nagata_Theorem
set_option autoImplicit false
open NagataFactoriality

theorem NagataFactoriality.ufd_of_factorization_and_prime_irreducibles {α : Type*} [CommRing α] [IsDomain α]
    (hfac : WfDvdMonoid α)
    (hprime : ∀ p : α, Irreducible p → Prime p) :
    UniqueFactorizationMonoid α := by sorry
