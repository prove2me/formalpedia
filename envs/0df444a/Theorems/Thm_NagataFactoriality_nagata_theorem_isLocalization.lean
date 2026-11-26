-- Prove2me | Theorems.Thm_NagataFactoriality_nagata_theorem_isLocalization
-- name    : NagataFactoriality.nagata_theorem_isLocalization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:58:51.307872+00:00
-- url     : https://prove2.me/theorems/eb9c422d-a351-40a4-9b86-8e5bb234df6c
-- title:
--   Nagata Factoriality: nagata theorem is Localization
-- statement:
--   The Nagata Factoriality construction uses the nagata theorem is Localization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Theorem.lean#L20-L27
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Theorem.lean#L20-L27

import Definitions.Def_NagataFactoriality_Nagata_Lemmas
import Definitions.Def_NagataFactoriality_Nagata_Theorem
set_option autoImplicit false
open NagataFactoriality

theorem NagataFactoriality.nagata_theorem_isLocalization {R T : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (S : Submonoid R) [CommRing T] [Algebra R T] [_root_.IsLocalization S T]
    [IsDomain T] (hS : PrimeGenerated S) (hUFD : UniqueFactorizationMonoid T) :
    UniqueFactorizationMonoid R := by sorry
