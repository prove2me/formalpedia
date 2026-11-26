-- Prove2me | Theorems.Thm_NagataFactoriality_nagata_theorem_of_prime_or_unit_isLocalization
-- name    : NagataFactoriality.nagata_theorem_of_prime_or_unit_isLocalization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:01:42.518051+00:00
-- url     : https://prove2.me/theorems/14f66f3f-4718-5a22-9f98-c41e4b6fc193
-- title:
--   Nagata Factoriality: nagata theorem of prime or unit is Localization
-- statement:
--   The Nagata Factoriality construction uses the nagata theorem of prime or unit is Localization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Theorem.lean#L84-L92
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Theorem.lean#L84-L92

import Definitions.Def_NagataFactoriality_Nagata_Lemmas
import Definitions.Def_NagataFactoriality_Nagata_Theorem
set_option autoImplicit false
open NagataFactoriality

theorem NagataFactoriality.nagata_theorem_of_prime_or_unit_isLocalization {R T : Type*}
    [CommRing R] [IsDomain R] [IsNoetherianRing R] (S : Submonoid R) [CommRing T] [Algebra R T]
    [_root_.IsLocalization S T] [IsDomain T]
    (hS : ∀ s ∈ S, Prime s ∨ IsUnit s) (hUFD : UniqueFactorizationMonoid T) :
    UniqueFactorizationMonoid R := by sorry
