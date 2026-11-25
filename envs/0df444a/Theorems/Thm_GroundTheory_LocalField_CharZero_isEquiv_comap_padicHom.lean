-- Prove2me | Theorems.Thm_GroundTheory_LocalField_CharZero_isEquiv_comap_padicHom
-- name    : GroundTheory.LocalField.CharZero.isEquiv_comap_padicHom
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:43:56.665026+00:00
-- url     : https://prove2.me/theorems/ccd5e2c1-d711-4094-b0a2-e59d43699528
-- title:
--   Char Zero: is Equiv comap padic Hom
-- statement:
--   The Char Zero construction uses the is Equiv comap padic Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExamplesCharZero.lean#L164-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExamplesCharZero.lean#L164-L168

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

theorem GroundTheory.LocalField.CharZero.isEquiv_comap_padicHom :
    ((valuation K).comap (padicHom K p)).IsEquiv Padic.mulValuation := by sorry
