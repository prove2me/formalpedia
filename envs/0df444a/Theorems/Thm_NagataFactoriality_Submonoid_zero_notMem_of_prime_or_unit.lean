-- Prove2me | Theorems.Thm_NagataFactoriality_Submonoid_zero_notMem_of_prime_or_unit
-- name    : NagataFactoriality.Submonoid.zero_notMem_of_prime_or_unit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:47:47.092816+00:00
-- url     : https://prove2.me/theorems/c905663a-6215-40fe-af37-6202898a8259
-- title:
--   Submonoid: zero not Mem of prime or unit
-- statement:
--   The Submonoid construction uses the zero not Mem of prime or unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/MultSet.lean#L9-L14
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/MultSet.lean#L9-L14

import Definitions.Def_NagataFactoriality_Basic_Divisibility
import Definitions.Def_NagataFactoriality_Localization_MultSet
set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.Submonoid
variable {α : Type*} [CommRing α] [IsDomain α]

theorem NagataFactoriality.Submonoid.zero_notMem_of_prime_or_unit {S : Submonoid α}
    (hS : ∀ s ∈ S, Prime s ∨ IsUnit s) : (0 : α) ∉ S := by sorry
