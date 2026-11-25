-- Prove2me | Theorems.Thm_GroundTheory_LocalField_PadicRank_valBallSubmodule_le_range
-- name    : GroundTheory.LocalField.PadicRank.valBallSubmodule_le_range
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:50:04.689149+00:00
-- url     : https://prove2.me/theorems/636a6fff-1f71-5d6d-8da6-11a6edead6b1
-- title:
--   Padic Rank: val Ball Submodule le range
-- statement:
--   The Padic Rank construction uses the val Ball Submodule le range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PrincipalUnitsRank.lean#L199-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PrincipalUnitsRank.lean#L199-L209

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

theorem GroundTheory.LocalField.PadicRank.valBallSubmodule_le_range : valBallSubmodule K p ((absRamificationIndex K + 1 : ℕ) : ℤ) ≤
    LinearMap.range (padicLogLinear K p) := by sorry
