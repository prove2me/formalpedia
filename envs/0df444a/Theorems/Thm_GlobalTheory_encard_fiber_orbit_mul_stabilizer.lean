-- Prove2me | Theorems.Thm_GlobalTheory_encard_fiber_orbit_mul_stabilizer
-- name    : GlobalTheory.encard_fiber_orbit_mul_stabilizer
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:49:24.726737+00:00
-- url     : https://prove2.me/theorems/f19d039a-82ca-5621-a03e-40f5dc1c991a
-- title:
--   Global Theory: encard fiber orbit mul stabilizer
-- statement:
--   The Global Theory construction uses the encard fiber orbit mul stabilizer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TsumInvStabilizerEqTsumMulFiber.lean#L9-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TsumInvStabilizerEqTsumMulFiber.lean#L9-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TsumInvStabilizerEqTsumMulFiber
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ENNReal
open GlobalTheory
open MulAction

theorem GlobalTheory.encard_fiber_orbit_mul_stabilizer {Γ L Y : Type} [Group Γ] [MulAction Γ L] [MulAction Γ Y]
    (π : L → Y) (hπ : ∀ (g : Γ) (x : L), π (g • x) = g • π x) (x : L) (y : Y) (g : Γ)
    (hg : g • π x = y) :
    ({z : L | π z = y ∧ z ∈ orbit Γ x}).encard * (stabilizer Γ x : Set Γ).encard
      = (stabilizer Γ y : Set Γ).encard := by sorry
