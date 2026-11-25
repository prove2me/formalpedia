-- Prove2me | Theorems.Thm_GroundTheory_LocalField_finrank_principalUnits
-- name    : GroundTheory.LocalField.finrank_principalUnits
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:00:32.189001+00:00
-- url     : https://prove2.me/theorems/9e6f5565-56c5-587d-881b-c4345a5a5e9d
-- title:
--   Local Field: finrank principal Units
-- statement:
--   The Local Field construction uses the finrank principal Units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PrincipalUnitsRank.lean#L268-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PrincipalUnitsRank.lean#L268-L290

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

theorem GroundTheory.LocalField.finrank_principalUnits (p : ℕ) [Fact p.Prime] [CharP 𝓀[K] p] [CharZero K] :
    Module.finrank ℤ_[p] (Additive (unitFiltrationUnits K 1)) =
      (letI := (CharZero.padicHom K p).toAlgebra; Module.finrank ℚ_[p] K) := by sorry
