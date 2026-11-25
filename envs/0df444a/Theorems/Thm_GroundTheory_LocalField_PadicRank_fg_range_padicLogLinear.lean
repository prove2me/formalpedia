-- Prove2me | Theorems.Thm_GroundTheory_LocalField_PadicRank_fg_range_padicLogLinear
-- name    : GroundTheory.LocalField.PadicRank.fg_range_padicLogLinear
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:52:25.706285+00:00
-- url     : https://prove2.me/theorems/8d3d6651-a605-4305-b252-f5394c6ce16c
-- title:
--   Padic Rank: fg range padic Log Linear
-- statement:
--   The Padic Rank construction uses the fg range padic Log Linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PrincipalUnitsRank.lean#L243-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PrincipalUnitsRank.lean#L243-L250

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

theorem GroundTheory.LocalField.PadicRank.fg_range_padicLogLinear : (LinearMap.range (padicLogLinear K p)).FG := by sorry
