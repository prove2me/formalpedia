-- Prove2me | Theorems.Thm_GroundTheory_LocalField_finite_principalUnits
-- name    : GroundTheory.LocalField.finite_principalUnits
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:00:40.556154+00:00
-- url     : https://prove2.me/theorems/13244456-64d3-5434-a3e8-71f9081273d5
-- title:
--   Local Field: finite principal Units
-- statement:
--   The Local Field construction uses the finite principal Units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PrincipalUnitsRank.lean#L260-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PrincipalUnitsRank.lean#L260-L266

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
open PadicRank
attribute [local instance] algebraK algebraInteger

theorem GroundTheory.LocalField.finite_principalUnits (p : ℕ) [Fact p.Prime] [CharP 𝓀[K] p] [CharZero K] :
    Module.Finite ℤ_[p] (Additive (unitFiltrationUnits K 1)) := by sorry
