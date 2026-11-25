-- Prove2me | Theorems.Thm_GroundTheory_LocalField_PadicRank_fg_ker_padicLogLinear
-- name    : GroundTheory.LocalField.PadicRank.fg_ker_padicLogLinear
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:45:37.024235+00:00
-- url     : https://prove2.me/theorems/7d8844c1-8b11-4e14-88a3-bf6166b831ba
-- title:
--   Padic Rank: fg ker padic Log Linear
-- statement:
--   The Padic Rank construction uses the fg ker padic Log Linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PrincipalUnitsRank.lean#L236-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PrincipalUnitsRank.lean#L236-L241

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

theorem GroundTheory.LocalField.PadicRank.fg_ker_padicLogLinear : (LinearMap.ker (padicLogLinear K p)).FG := by sorry
