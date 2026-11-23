-- Prove2me | Theorems.Thm_GroundTheory_LocalField_augmentation_eq_range
-- name    : GroundTheory.LocalField.augmentation_eq_range
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:16.064876+00:00
-- url     : https://prove2.me/theorems/ac6eacb9-eea0-482c-a62d-f09b4c492949
-- title:
--   Local Field: augmentation eq range
-- statement:
--   The Local Field construction uses the augmentation eq range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivial.lean#L64-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivial.lean#L64-L73

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

theorem GroundTheory.LocalField.augmentation_eq_range : augmentation G M = (augMap G M).range := by sorry
