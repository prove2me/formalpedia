-- Prove2me | Theorems.Thm_GroundTheory_LocalField_padicLog_mem_valBall_of_mem
-- name    : GroundTheory.LocalField.padicLog_mem_valBall_of_mem
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T06:19:37.833298+00:00
-- url     : https://prove2.me/theorems/ee39a31f-af64-4c5c-adc7-ded49a8d724e
-- title:
--   Local Field: padic Log mem val Ball of mem
-- statement:
--   The Local Field construction uses the padic Log mem val Ball of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PadicLogLinear.lean#L32-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PadicLogLinear.lean#L32-L40

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PrincipalUnitsModule
import Definitions.Def_GroundTheory_LocalFields_PadicLogLinear
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
variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p] [CharZero K]
include p

theorem GroundTheory.LocalField.padicLog_mem_valBall_of_mem {k : ℕ} (hk : absRamificationIndex K ≤ k)
    {w : Additive (unitFiltrationUnits K 1)} (hw : w ∈ principalFiltration K k) :
    padicLog K w ∈ valBall K (k + 1) := by sorry
