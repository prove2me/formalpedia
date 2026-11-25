-- Prove2me | Theorems.Thm_GroundTheory_LocalField_openCompletion_denseRange_of
-- name    : GroundTheory.LocalField.openCompletion.denseRange_of
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:00:35.956678+00:00
-- url     : https://prove2.me/theorems/53f720b4-1772-44ab-98d4-2529aa74c93d
-- title:
--   open Completion: dense Range of
-- statement:
--   The open Completion construction uses the dense Range of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/OpenCompletion.lean#L97-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/OpenCompletion.lean#L97-L119

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

theorem GroundTheory.LocalField.openCompletion.denseRange_of : DenseRange (of G) := by sorry
