-- Prove2me | Theorems.Thm_NagataFactoriality_nagata_theorem_of_finite_prime_generators
-- name    : NagataFactoriality.nagata_theorem_of_finite_prime_generators
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:01:37.998724+00:00
-- url     : https://prove2.me/theorems/2ee7fd49-5376-4249-a4ac-d6cf4210d4eb
-- title:
--   Nagata Factoriality: nagata theorem of finite prime generators
-- statement:
--   The Nagata Factoriality construction uses the nagata theorem of finite prime generators property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Theorem.lean#L48-L59
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Theorem.lean#L48-L59

import Definitions.Def_NagataFactoriality_Nagata_Lemmas
import Definitions.Def_NagataFactoriality_Nagata_Theorem
import Theorems.Thm_NagataFactoriality_primeGenerated_closure_finset_of_primes

set_option autoImplicit false
open NagataFactoriality

theorem NagataFactoriality.nagata_theorem_of_finite_prime_generators {R : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (s : Finset R) (hs : ∀ q ∈ s, Prime q)
    (hUFD :
      @UniqueFactorizationMonoid (Localization (Submonoid.closure (↑s : Set R)))
        (by
          let hS : PrimeGenerated (Submonoid.closure (↑s : Set R)) :=
            primeGenerated_closure_finset_of_primes s hs
          letI : Fact ((0 : R) ∉ Submonoid.closure (↑s : Set R)) :=
            ⟨zero_notMem_of_primeGenerated hS⟩
          infer_instance)) :
    UniqueFactorizationMonoid R := by sorry
