-- Prove2me | Theorems.Thm_GroundTheory_LocalField_IsElementary_mono
-- name    : GroundTheory.LocalField.IsElementary.mono
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:35:26.229782+00:00
-- url     : https://prove2.me/theorems/a51d35a3-ebaf-4772-a2bc-df569386d243
-- title:
--   Is Elementary: mono
-- statement:
--   The Is Elementary construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionAssembly.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionAssembly.lean#L17-L19

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionPrime
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionAssembly
import Theorems.Thm_GroundTheory_LocalField_IsElementaryAt_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open Module Representation
open scoped Classical
universe u
variable {G : Type u} [Group G] [Fintype G]
omit [Fintype G]

theorem GroundTheory.LocalField.IsElementary.mono {H L : Subgroup G} (hH : IsElementary H) (hLH : L ≤ H) : IsElementary L := by sorry
