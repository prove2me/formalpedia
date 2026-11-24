-- Prove2me | Theorems.Thm_GlobalTheory_LOneLower_lambert_lower
-- name    : GlobalTheory.LOneLower.lambert_lower
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:56:19.380166+00:00
-- url     : https://prove2.me/theorems/f2b865a0-8014-439d-9306-8b59412aefa1
-- title:
--   LOne Lower: lambert lower
-- statement:
--   The LOne Lower construction uses the lambert lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsLeNormLFunctionOne.lean#L175-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsLeNormLFunctionOne.lean#L175-L238

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsLeNormLFunctionOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Filter Topology
open scoped ComplexOrder
open GlobalTheory GlobalTheory.LOneLower

theorem GlobalTheory.LOneLower.lambert_lower {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ : χ ^ 2 = 1) {M : ℕ}
    (hM : 0 < M) :
    (M : ℝ) / 3 ≤ ‖∑' d : ℕ, χ ((d + 1 : ℕ) : ZMod q) *
      (((Real.exp (((d + 1 : ℕ) : ℝ) * ((M : ℝ) ^ 2)⁻¹) - 1)⁻¹ : ℝ) : ℂ)‖ := by sorry
