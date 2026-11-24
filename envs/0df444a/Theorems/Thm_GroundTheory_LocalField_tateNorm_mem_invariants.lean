-- Prove2me | Theorems.Thm_GroundTheory_LocalField_tateNorm_mem_invariants
-- name    : GroundTheory.LocalField.tateNorm_mem_invariants
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:44:51.072363+00:00
-- url     : https://prove2.me/theorems/c9f17794-3670-4574-bdd2-8a5fb9a8b5b4
-- title:
--   Local Field: tate Norm mem invariants
-- statement:
--   The Local Field construction uses the tate Norm mem invariants property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivial.lean#L56-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivial.lean#L56-L57

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

theorem GroundTheory.LocalField.tateNorm_mem_invariants (x : M) : tateNorm G M x ∈ invariants G M := by sorry
