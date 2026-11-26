-- Prove2me | Theorems.Thm_NagataFactoriality_nagata_key_lemma_primeGenerated
-- name    : NagataFactoriality.nagata_key_lemma_primeGenerated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:00:47.006128+00:00
-- url     : https://prove2.me/theorems/8b2efd40-7647-509f-84cb-a966188e311c
-- title:
--   Nagata Factoriality: nagata key lemma prime Generated
-- statement:
--   The Nagata Factoriality construction uses the nagata key lemma prime Generated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Lemmas.lean#L391-L404
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Lemmas.lean#L391-L404

import Definitions.Def_NagataFactoriality_Localization_Properties
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
import Definitions.Def_NagataFactoriality_Basic_UFD
import Definitions.Def_NagataFactoriality_Nagata_Lemmas
set_option autoImplicit false
open NagataFactoriality

theorem NagataFactoriality.nagata_key_lemma_primeGenerated {α : Type*} [CommRing α] [IsDomain α] {S : Submonoid α}
    (hS : PrimeGenerated S)
    (hUFD :
      @UniqueFactorizationMonoid (Localization S)
        (by
          letI : Fact ((0 : α) ∉ S) := ⟨zero_notMem_of_primeGenerated hS⟩
          infer_instance))
    {p : α} (hp : Irreducible p) : Prime p := by sorry
