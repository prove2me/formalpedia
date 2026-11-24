-- Prove2me | Theorems.Thm_GlobalTheory_LOneLower_lambert
-- name    : GlobalTheory.LOneLower.lambert
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:56:12.365099+00:00
-- url     : https://prove2.me/theorems/2f2d8162-465a-4dbe-92ce-db4138cb9912
-- title:
--   LOne Lower: lambert
-- statement:
--   The LOne Lower construction uses the lambert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsLeNormLFunctionOne.lean#L140-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsLeNormLFunctionOne.lean#L140-L173

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

theorem GlobalTheory.LOneLower.lambert {q : ℕ} (χ : DirichletCharacter ℂ q) {t : ℂ} (ht : ‖t‖ < 1) :
    HasSum (fun n : ℕ+ => zetaMul χ n * t ^ (n : ℕ))
      (∑' d : ℕ+, χ ((d : ℕ) : ZMod q) * (t ^ (d : ℕ) / (1 - t ^ (d : ℕ)))) := by sorry
