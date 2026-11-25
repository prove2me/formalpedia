-- Prove2me | Theorems.Thm_GlobalTheory_DI_logLift_of_unit_mem_map
-- name    : GlobalTheory.DI.logLift_of_unit_mem_map
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:03:44.098692+00:00
-- url     : https://prove2.me/theorems/e84622eb-dc52-4d17-9c56-09ff8d81b00f
-- title:
--   DI: log Lift of unit mem map
-- statement:
--   The DI construction uses the log Lift of unit mem map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LogLiftOfUnitMemMap.lean#L10-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LogLiftOfUnitMemMap.lean#L10-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LogLiftOfUnitMemMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
set_option autoImplicit false

theorem GlobalTheory.DI.logLift_of_unit_mem_map : ∀ {K Kt : Type} [Field K] [CommRing Kt] (p : ℕ) [Fact p.Prime] [CharP K p]
    (π : Kt →+* K) {ι : Type} (F : ι → Kt →+* Kt) (s : Finset ι) (At : Subring Kt), _root_.GlobalTheory.DI.IsFlatLift p π →
    (∀ i ∈ s, ∀ z ∈ At, ∃ w ∈ At, F i z = z ^ p + p * w) → ∀ g : K, g ≠ 0 → g ∈ At.map π →
    g⁻¹ ∈ At.map π → _root_.GlobalTheory.DI.LogLift p π F s (At.map π : Set K) g := by sorry
