-- Prove2me | Theorems.Thm_GroundTheory_LocalField_CharZero_valuation_padicHom_padicInt_le_one
-- name    : GroundTheory.LocalField.CharZero.valuation_padicHom_padicInt_le_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:38:08.564234+00:00
-- url     : https://prove2.me/theorems/a228bc33-a9c0-4679-877f-5bf5081e5da6
-- title:
--   Char Zero: valuation padic Hom padic Int le one
-- statement:
--   The Char Zero construction uses the valuation padic Hom padic Int le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExamplesCharZero.lean#L123-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExamplesCharZero.lean#L123-L128

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

theorem GroundTheory.LocalField.CharZero.valuation_padicHom_padicInt_le_one (x : ℤ_[p]) :
    valuation K (padicHom K p (x : ℚ_[p])) ≤ 1 := by sorry
