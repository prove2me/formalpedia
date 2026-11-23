-- Prove2me | Theorems.Thm_GroundTheory_LocalField_subsingleton_tateNegOne_iff
-- name    : GroundTheory.LocalField.subsingleton_tateNegOne_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:19:17.678269+00:00
-- url     : https://prove2.me/theorems/2ed36db9-20c7-4ca4-a9b4-9c138b2eb61d
-- title:
--   Local Field: subsingleton tate Neg One iff
-- statement:
--   The Local Field construction uses the subsingleton tate Neg One iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivial.lean#L80-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivial.lean#L80-L83

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

theorem GroundTheory.LocalField.subsingleton_tateNegOne_iff :
    Subsingleton (TateNegOne G M) ↔ ∀ x : M, tateNorm G M x = 1 → x ∈ augmentation G M := by sorry
