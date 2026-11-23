-- Prove2me | Theorems.Thm_GroundTheory_LocalField_IsElementaryAt_mono
-- name    : GroundTheory.LocalField.IsElementaryAt.mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:50:19.616098+00:00
-- url     : https://prove2.me/theorems/324afbc1-752b-4236-b9a3-550a3c783257
-- title:
--   Is Elementary At: mono
-- statement:
--   The Is Elementary At construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionElementary.lean#L65-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionElementary.lean#L65-L92

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionElementary
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
variable {G : Type*} [Group G]
variable [Finite G] {p : ℕ}
omit [Finite G]

theorem GroundTheory.LocalField.IsElementaryAt.mono {H L : Subgroup G} (hH : IsElementaryAt p H) (hLH : L ≤ H) :
    IsElementaryAt p L := by sorry
