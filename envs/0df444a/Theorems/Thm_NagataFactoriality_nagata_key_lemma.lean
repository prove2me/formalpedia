-- Prove2me | Theorems.Thm_NagataFactoriality_nagata_key_lemma
-- name    : NagataFactoriality.nagata_key_lemma
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:01:34.336267+00:00
-- url     : https://prove2.me/theorems/3f1f6d6f-27b9-493b-a2a2-abba68ce5c81
-- title:
--   Nagata Factoriality: nagata key lemma
-- statement:
--   The Nagata Factoriality construction uses the nagata key lemma property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Lemmas.lean#L636-L649
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Lemmas.lean#L636-L649

import Definitions.Def_NagataFactoriality_Localization_Properties
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
import Definitions.Def_NagataFactoriality_Basic_UFD
import Definitions.Def_NagataFactoriality_Nagata_Lemmas
set_option autoImplicit false
open NagataFactoriality

theorem NagataFactoriality.nagata_key_lemma {α : Type*} [CommRing α] [IsDomain α] {S : Submonoid α}
    (hS : ∀ s ∈ S, Prime s ∨ IsUnit s)
    (hUFD :
      @UniqueFactorizationMonoid (Localization S)
        (by
          letI : Fact ((0 : α) ∉ S) := submonoidZeroNotMemFact hS
          infer_instance))
    {p : α} (hp : Irreducible p) : Prime p := by sorry
