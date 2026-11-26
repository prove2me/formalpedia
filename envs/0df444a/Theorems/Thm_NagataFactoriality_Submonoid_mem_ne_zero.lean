-- Prove2me | Theorems.Thm_NagataFactoriality_Submonoid_mem_ne_zero
-- name    : NagataFactoriality.Submonoid.mem_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:48:52.690944+00:00
-- url     : https://prove2.me/theorems/c1f50990-ea74-4d24-a67d-ec76d3a4eb4e
-- title:
--   Submonoid: mem ne zero
-- statement:
--   The Submonoid construction uses the mem ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/MultSet.lean#L17-L20
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/MultSet.lean#L17-L20

import Definitions.Def_NagataFactoriality_Basic_Divisibility
import Definitions.Def_NagataFactoriality_Localization_MultSet
set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.Submonoid
variable {α : Type*} [CommRing α] [IsDomain α]
omit [IsDomain α]

theorem NagataFactoriality.Submonoid.mem_ne_zero {S : Submonoid α} [Fact ((0 : α) ∉ S)] {s : α} (hs : s ∈ S) : s ≠ 0 := by sorry
