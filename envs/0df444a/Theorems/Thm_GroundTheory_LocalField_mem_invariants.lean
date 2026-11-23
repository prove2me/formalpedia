-- Prove2me | Theorems.Thm_GroundTheory_LocalField_mem_invariants
-- name    : GroundTheory.LocalField.mem_invariants
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:49.03533+00:00
-- url     : https://prove2.me/theorems/4b79b1a4-3b17-494a-a614-8223a05fcff4
-- title:
--   Local Field: mem invariants
-- statement:
--   The Local Field construction uses the mem invariants property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivial.lean#L26-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivial.lean#L26-L26

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
omit [Fintype G]

theorem GroundTheory.LocalField.mem_invariants {x : M} : x ∈ invariants G M ↔ ∀ g : G, g • x = x := by sorry
