-- Prove2me | Theorems.Thm_GroundTheory_LocalField_CharZero_valuation_padicHom_le_one_iff
-- name    : GroundTheory.LocalField.CharZero.valuation_padicHom_le_one_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:43:58.264658+00:00
-- url     : https://prove2.me/theorems/45a45b92-752d-44db-9719-6487c371a479
-- title:
--   Char Zero: valuation padic Hom le one iff
-- statement:
--   The Char Zero construction uses the valuation padic Hom le one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExamplesCharZero.lean#L130-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExamplesCharZero.lean#L130-L162

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Examples
import Definitions.Def_GroundTheory_LocalFields_ExamplesCharZero
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
open ValuativeRel WithZero Topology
open GroundTheory.LocalField.CharZero
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (p : ℕ) [CharP 𝓀[K] p]
variable [Fact p.Prime]
variable [CharZero K]

theorem GroundTheory.LocalField.CharZero.valuation_padicHom_le_one_iff (x : ℚ_[p]) :
    valuation K (padicHom K p x) ≤ 1 ↔ ‖x‖ ≤ 1 := by sorry
