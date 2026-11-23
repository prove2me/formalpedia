-- Prove2me | Theorems.Thm_GlobalTheory_Mem_nonempty_rayData_of_ne_zero
-- name    : GlobalTheory.Mem.nonempty_rayData_of_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:50.681569+00:00
-- url     : https://prove2.me/theorems/c2cce100-796a-4679-bdac-e3f46062d93e
-- title:
--   Mem: nonempty ray Data of ne zero
-- statement:
--   The Mem construction uses the nonempty ray Data of ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/NonemptyRayDataOfNeZero.lean#L213-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/NonemptyRayDataOfNeZero.lean#L213-L213

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Mem
open NumberField IsDedekindDomain
attribute [instance] RayData.grp RayData.fin

theorem GlobalTheory.Mem.nonempty_rayData_of_ne_zero (K : Type) [Field K] [NumberField K] (M : ℕ) (hM : M ≠ 0) : Nonempty (RayData K M) := by sorry
