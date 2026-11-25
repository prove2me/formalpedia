-- Prove2me | Theorems.Thm_GroundTheory_LocalField_PadicRank_range_padicLogLinear_le
-- name    : GroundTheory.LocalField.PadicRank.range_padicLogLinear_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:44:56.590868+00:00
-- url     : https://prove2.me/theorems/72f7e409-5839-4c98-9aaa-a216f580ee4b
-- title:
--   Padic Rank: range padic Log Linear le
-- statement:
--   The Padic Rank construction uses the range padic Log Linear le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PrincipalUnitsRank.lean#L186-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PrincipalUnitsRank.lean#L186-L190

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PadicLogLinear
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_PrincipalUnitsRank
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
open ValuativeRel IsLocalRing Topology Filter
open scoped WithZero
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
open GroundTheory.LocalField.PadicRank
variable (p : ℕ) [hp : Fact p.Prime]
variable [CharP 𝓀[K] p] [CharZero K]
attribute [local instance] algebraK algebraInteger

theorem GroundTheory.LocalField.PadicRank.range_padicLogLinear_le : LinearMap.range (padicLogLinear K p) ≤
    valBallSubmodule K p (absRamificationIndex K + 1 -
      absRamificationIndex K * absRamificationIndex K) := by sorry
