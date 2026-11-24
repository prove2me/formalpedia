-- Prove2me | Theorems.Thm_GlobalTheory_norm_ratCast_eq_padicNorm
-- name    : GlobalTheory.norm_ratCast_eq_padicNorm
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:13:00.219744+00:00
-- url     : https://prove2.me/theorems/562a6623-c45a-4f1a-b337-3bbc36fc2c02
-- title:
--   Global Theory: norm rat Cast eq padic Norm
-- statement:
--   The Global Theory construction uses the norm rat Cast eq padic Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAbsoluteValueOfIsDiscreteValuationRing.lean#L365-L396
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAbsoluteValueOfIsDiscreteValuationRing.lean#L365-L396

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowLeComapMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
universe u

theorem GlobalTheory.norm_ratCast_eq_padicNorm {C : Type*} [NormedField C] [IsUltrametricDist C] [CharZero C]
    (p : ℕ) [hp : Fact p.Prime] (h : ‖(p : C)‖ = (p : ℝ)⁻¹) (q : ℚ) :
    ‖(q : C)‖ = ‖(q : ℚ_[p])‖ := by sorry
