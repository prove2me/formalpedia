-- Prove2me | Theorems.Thm_NagataFactoriality_Submonoid_le_nonZeroDivisors
-- name    : NagataFactoriality.Submonoid.le_nonZeroDivisors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:47:41.787961+00:00
-- url     : https://prove2.me/theorems/5e14320c-d565-57c3-a621-929dc334196a
-- title:
--   Submonoid: le non Zero Divisors
-- statement:
--   The Submonoid construction uses the le non Zero Divisors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/MultSet.lean#L22-L26
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/MultSet.lean#L22-L26

import Definitions.Def_NagataFactoriality_Basic_Divisibility
import Definitions.Def_NagataFactoriality_Localization_MultSet
set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.Submonoid
variable {α : Type*} [CommRing α] [IsDomain α]

theorem NagataFactoriality.Submonoid.le_nonZeroDivisors {S : Submonoid α} [Fact ((0 : α) ∉ S)] :
    S ≤ nonZeroDivisors α := by sorry
