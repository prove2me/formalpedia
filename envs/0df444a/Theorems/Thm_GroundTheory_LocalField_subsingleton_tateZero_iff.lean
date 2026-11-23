-- Prove2me | Theorems.Thm_GroundTheory_LocalField_subsingleton_tateZero_iff
-- name    : GroundTheory.LocalField.subsingleton_tateZero_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:39.493794+00:00
-- url     : https://prove2.me/theorems/dc9301c2-7fef-47ba-81ef-600b6ddff8e0
-- title:
--   Local Field: subsingleton tate Zero iff
-- statement:
--   The Local Field construction uses the subsingleton tate Zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivial.lean#L75-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivial.lean#L75-L78

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open Finset Filter
variable (G M : Type*) [Group G] [Fintype G] [CommGroup M] [MulDistribMulAction G M]
variable {G M}

theorem GroundTheory.LocalField.subsingleton_tateZero_iff :
    Subsingleton (TateZero G M) ↔ ∀ x : M, (∀ g : G, g • x = x) → ∃ y, tateNorm G M y = x := by sorry
