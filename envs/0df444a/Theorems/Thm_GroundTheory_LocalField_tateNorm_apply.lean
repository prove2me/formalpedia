-- Prove2me | Theorems.Thm_GroundTheory_LocalField_tateNorm_apply
-- name    : GroundTheory.LocalField.tateNorm_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:35.521901+00:00
-- url     : https://prove2.me/theorems/d4bfb875-2dd4-4503-848e-b0e5cdad9f6c
-- title:
--   Local Field: tate Norm apply
-- statement:
--   The Local Field construction uses the tate Norm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivial.lean#L17-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivial.lean#L17-L17

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

theorem GroundTheory.LocalField.tateNorm_apply (x : M) : tateNorm G M x = ∏ g : G, g • x := by sorry
