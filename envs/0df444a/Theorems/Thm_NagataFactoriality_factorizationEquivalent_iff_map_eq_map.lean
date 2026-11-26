-- Prove2me | Theorems.Thm_NagataFactoriality_factorizationEquivalent_iff_map_eq_map
-- name    : NagataFactoriality.factorizationEquivalent_iff_map_eq_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:49:26.991855+00:00
-- url     : https://prove2.me/theorems/561b3299-31ce-4376-b289-33fa16582b80
-- title:
--   Nagata Factoriality: factorization Equivalent iff map eq map
-- statement:
--   The Nagata Factoriality construction uses the factorization Equivalent iff map eq map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Basic/UFD.lean#L37-L39
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Basic/UFD.lean#L37-L39

import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Definitions.Def_NagataFactoriality_Basic_Noetherian
import Definitions.Def_NagataFactoriality_Basic_UFD
set_option autoImplicit false
open NagataFactoriality

theorem NagataFactoriality.factorizationEquivalent_iff_map_eq_map {α : Type*} [CommMonoid α] {f g : Multiset α} :
    FactorizationEquivalent f g ↔ f.map Associates.mk = g.map Associates.mk := by sorry
