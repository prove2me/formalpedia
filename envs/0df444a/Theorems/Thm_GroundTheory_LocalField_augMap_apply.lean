-- Prove2me | Theorems.Thm_GroundTheory_LocalField_augMap_apply
-- name    : GroundTheory.LocalField.augMap_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:41.640795+00:00
-- url     : https://prove2.me/theorems/aad485aa-bc85-4635-8f29-8f967c14ae4a
-- title:
--   Local Field: aug Map apply
-- statement:
--   The Local Field construction uses the aug Map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivial.lean#L43-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivial.lean#L43-L43

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

theorem GroundTheory.LocalField.augMap_apply (m : G → M) : augMap G M m = ∏ g : G, g • m g / m g := by sorry
