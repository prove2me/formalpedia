-- Prove2me | Theorems.Thm_GroundTheory_LocalField_openCompletion_apply_eq
-- name    : GroundTheory.LocalField.openCompletion.apply_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:45:02.820032+00:00
-- url     : https://prove2.me/theorems/820a9e58-42fe-40f8-b536-20ae5414bfc2
-- title:
--   open Completion: apply eq
-- statement:
--   The open Completion construction uses the apply eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/OpenCompletion.lean#L41-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/OpenCompletion.lean#L41-L44

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

theorem GroundTheory.LocalField.openCompletion.apply_eq (a : openCompletion G) {H H' : openFiniteIndex G} (h : (H : Subgroup G) ≤ H') :
    quotientMapOfLE h ((a : ∀ H : openFiniteIndex G, G ⧸ (H : Subgroup G)) H) =
      (a : ∀ H : openFiniteIndex G, G ⧸ (H : Subgroup G)) H' := by sorry
