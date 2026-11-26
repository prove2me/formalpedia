-- Prove2me | Theorems.Thm_NagataFactoriality_nagata_theorem_of_prime_or_unit
-- name    : NagataFactoriality.nagata_theorem_of_prime_or_unit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:01:51.780937+00:00
-- url     : https://prove2.me/theorems/c901feed-f29f-4045-a0f9-11842142cd5d
-- title:
--   Nagata Factoriality: nagata theorem of prime or unit
-- statement:
--   The Nagata Factoriality construction uses the nagata theorem of prime or unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Theorem.lean#L69-L82
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Theorem.lean#L69-L82

import Definitions.Def_NagataFactoriality_Nagata_Lemmas
import Definitions.Def_NagataFactoriality_Nagata_Theorem
import Theorems.Thm_NagataFactoriality_Submonoid_zero_notMem_of_prime_or_unit

set_option autoImplicit false
open NagataFactoriality

theorem NagataFactoriality.nagata_theorem_of_prime_or_unit {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (S : Submonoid R) (hS : ∀ s ∈ S, Prime s ∨ IsUnit s)
    (hUFD :
      @UniqueFactorizationMonoid (Localization S)
        (by
          letI : Fact ((0 : R) ∉ S) := ⟨Submonoid.zero_notMem_of_prime_or_unit hS⟩
          infer_instance)) :
    UniqueFactorizationMonoid R := by sorry
