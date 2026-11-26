-- Prove2me | Theorems.Thm_NagataFactoriality_nagata_theorem_of_prime_generators
-- name    : NagataFactoriality.nagata_theorem_of_prime_generators
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:59:55.178657+00:00
-- url     : https://prove2.me/theorems/a3576c75-6e97-4f4b-8de3-90c3ca25c0f8
-- title:
--   Nagata Factoriality: nagata theorem of prime generators
-- statement:
--   The Nagata Factoriality construction uses the nagata theorem of prime generators property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Theorem.lean#L29-L38
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Theorem.lean#L29-L38

import Definitions.Def_NagataFactoriality_Nagata_Lemmas
import Definitions.Def_NagataFactoriality_Nagata_Theorem
import Theorems.Thm_NagataFactoriality_primeGenerated_closure_of_primes

set_option autoImplicit false
open NagataFactoriality

theorem NagataFactoriality.nagata_theorem_of_prime_generators {R : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (s : Set R) (hs : ∀ q ∈ s, Prime q)
    (hUFD :
      @UniqueFactorizationMonoid (Localization (Submonoid.closure s))
        (by
          let hS : PrimeGenerated (Submonoid.closure s) := primeGenerated_closure_of_primes hs
          letI : Fact ((0 : R) ∉ Submonoid.closure s) := ⟨zero_notMem_of_primeGenerated hS⟩
          infer_instance)) :
    UniqueFactorizationMonoid R := by sorry
