-- Prove2me | Theorems.Thm_NagataFactoriality_nagata_theorem_of_prime_generators_isLocalization
-- name    : NagataFactoriality.nagata_theorem_of_prime_generators_isLocalization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:58:57.798+00:00
-- url     : https://prove2.me/theorems/bac5dbe9-70c9-59fc-8e53-852344095926
-- title:
--   Nagata Factoriality: nagata theorem of prime generators is Localization
-- statement:
--   The Nagata Factoriality construction uses the nagata theorem of prime generators is Localization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Theorem.lean#L40-L46
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Theorem.lean#L40-L46

import Definitions.Def_NagataFactoriality_Nagata_Lemmas
import Definitions.Def_NagataFactoriality_Nagata_Theorem
set_option autoImplicit false
open NagataFactoriality

theorem NagataFactoriality.nagata_theorem_of_prime_generators_isLocalization {R T : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (s : Set R) [CommRing T] [Algebra R T]
    [_root_.IsLocalization (Submonoid.closure s) T] [IsDomain T]
    (hs : ∀ q ∈ s, Prime q) (hUFD : UniqueFactorizationMonoid T) :
    UniqueFactorizationMonoid R := by sorry
