-- Prove2me | Theorems.Thm_NagataFactoriality_nagata_theorem_of_finite_prime_generators_isLocalization
-- name    : NagataFactoriality.nagata_theorem_of_finite_prime_generators_isLocalization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:01:33.158828+00:00
-- url     : https://prove2.me/theorems/7098af89-05e9-4c6f-a7b7-436c8769c414
-- title:
--   Nagata Factoriality: nagata theorem of finite prime generators is Localization
-- statement:
--   The Nagata Factoriality construction uses the nagata theorem of finite prime generators is Localization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Theorem.lean#L61-L67
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Theorem.lean#L61-L67

import Definitions.Def_NagataFactoriality_Nagata_Lemmas
import Definitions.Def_NagataFactoriality_Nagata_Theorem
set_option autoImplicit false
open NagataFactoriality

theorem NagataFactoriality.nagata_theorem_of_finite_prime_generators_isLocalization {R T : Type*}
    [CommRing R] [IsDomain R] [IsNoetherianRing R] (s : Finset R) [CommRing T] [Algebra R T]
    [_root_.IsLocalization (Submonoid.closure (↑s : Set R)) T] [IsDomain T]
    (hs : ∀ q ∈ s, Prime q) (hUFD : UniqueFactorizationMonoid T) :
    UniqueFactorizationMonoid R := by sorry
