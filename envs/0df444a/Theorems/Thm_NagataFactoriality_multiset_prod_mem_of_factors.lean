-- Prove2me | Theorems.Thm_NagataFactoriality_multiset_prod_mem_of_factors
-- name    : NagataFactoriality.multiset_prod_mem_of_factors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:58:32.042262+00:00
-- url     : https://prove2.me/theorems/233dd7d5-f338-4364-8c21-5d7d42bc3ca7
-- title:
--   Nagata Factoriality: multiset prod mem of factors
-- statement:
--   The Nagata Factoriality construction uses the multiset prod mem of factors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Lemmas.lean#L177-L188
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Nagata/Lemmas.lean#L177-L188

import Definitions.Def_NagataFactoriality_Localization_Properties
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
import Definitions.Def_NagataFactoriality_Basic_UFD
import Definitions.Def_NagataFactoriality_Nagata_Lemmas
set_option autoImplicit false
open NagataFactoriality

theorem NagataFactoriality.multiset_prod_mem_of_factors {α : Type*} [CommMonoid α] {S : Submonoid α} {f : Multiset α}
    (hf : ∀ q ∈ f, q ∈ S) : f.prod ∈ S := by sorry
