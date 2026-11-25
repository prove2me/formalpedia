-- Prove2me | Theorems.Thm_GroundTheory_LocalField_openCompletion_mem_iff
-- name    : GroundTheory.LocalField.openCompletion.mem_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:00:30.035349+00:00
-- url     : https://prove2.me/theorems/15f13308-3a91-4cb4-9e84-09190352799b
-- title:
--   open Completion: mem iff
-- statement:
--   The open Completion construction uses the mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/OpenCompletion.lean#L35-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/OpenCompletion.lean#L35-L38

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_OpenCompletion
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
variable (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
open GroundTheory.LocalField.openCompletion
variable {G}
omit [IsTopologicalGroup G]

theorem GroundTheory.LocalField.openCompletion.mem_iff {a : ∀ H : openFiniteIndex G, G ⧸ (H : Subgroup G)} :
    a ∈ openCompletion G ↔
      ∀ (H H' : openFiniteIndex G) (h : (H : Subgroup G) ≤ H'), quotientMapOfLE h (a H) = a H' := by sorry
