-- Prove2me | Theorems.Thm_NagataFactoriality_nagata_theorem
-- name    : NagataFactoriality.nagata_theorem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:58:58.307365+00:00
-- url     : https://prove2.me/theorems/43cb71d5-39a5-523c-b86f-6f94ac433005
-- title:
--   Nagata Factoriality: nagata theorem
-- statement:
--   The Nagata Factoriality construction uses the nagata theorem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Theorem.lean#L5-L18
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Theorem.lean#L5-L18

import Definitions.Def_NagataFactoriality_Nagata_Lemmas
import Definitions.Def_NagataFactoriality_Nagata_Theorem
set_option autoImplicit false
open NagataFactoriality

theorem NagataFactoriality.nagata_theorem {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (S : Submonoid R) (hS : PrimeGenerated S)
    (hUFD :
      @UniqueFactorizationMonoid (Localization S)
        (by
          letI : Fact ((0 : R) ∉ S) := ⟨zero_notMem_of_primeGenerated hS⟩
          infer_instance)) :
    UniqueFactorizationMonoid R := by sorry
