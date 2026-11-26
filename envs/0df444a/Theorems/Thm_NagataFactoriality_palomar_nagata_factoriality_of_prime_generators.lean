-- Prove2me | Theorems.Thm_NagataFactoriality_palomar_nagata_factoriality_of_prime_generators
-- name    : NagataFactoriality.palomar_nagata_factoriality_of_prime_generators
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:02:36.596823+00:00
-- url     : https://prove2.me/theorems/f1d81628-0c88-5cb6-9a8c-d6fd5d73cd7e
-- title:
--   Nagata Factoriality: palomar nagata factoriality of prime generators
-- statement:
--   The Nagata Factoriality construction uses the palomar nagata factoriality of prime generators property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/Solution.lean#L24-L31
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/Solution.lean#L24-L31

import Definitions.Def_NagataFactoriality_Applications_Laurent
import Definitions.Def_NagataFactoriality_Solution
set_option autoImplicit false
open NagataFactoriality
open Polynomial

theorem NagataFactoriality.palomar_nagata_factoriality_of_prime_generators
    {R T : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (s : Set R) [CommRing T] [Algebra R T]
    [_root_.IsLocalization (Submonoid.closure s) T] [IsDomain T]
    (hs : ∀ q ∈ s, Prime q) (hUFD : UniqueFactorizationMonoid T) :
    UniqueFactorizationMonoid R := by sorry
