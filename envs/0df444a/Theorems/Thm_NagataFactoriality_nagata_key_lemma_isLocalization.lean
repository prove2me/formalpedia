-- Prove2me | Theorems.Thm_NagataFactoriality_nagata_key_lemma_isLocalization
-- name    : NagataFactoriality.nagata_key_lemma_isLocalization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:58:30.236146+00:00
-- url     : https://prove2.me/theorems/8368ab7b-1475-4f84-84b1-8872da6eed5c
-- title:
--   Nagata Factoriality: nagata key lemma is Localization
-- statement:
--   The Nagata Factoriality construction uses the nagata key lemma is Localization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Lemmas.lean#L617-L634
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Lemmas.lean#L617-L634

import Definitions.Def_NagataFactoriality_Localization_Properties
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
import Definitions.Def_NagataFactoriality_Basic_UFD
import Definitions.Def_NagataFactoriality_Nagata_Lemmas
set_option autoImplicit false
open NagataFactoriality

theorem NagataFactoriality.nagata_key_lemma_isLocalization {α β : Type*}
    [CommRing α] [IsDomain α] {S : Submonoid α} [CommRing β] [Algebra α β] [IsDomain β]
    [_root_.IsLocalization S β] (hS : ∀ s ∈ S, Prime s ∨ IsUnit s)
    [UniqueFactorizationMonoid β] {p : α} (hp : Irreducible p) : Prime p := by sorry
