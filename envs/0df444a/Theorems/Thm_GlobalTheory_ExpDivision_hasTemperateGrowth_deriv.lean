-- Prove2me | Theorems.Thm_GlobalTheory_ExpDivision_hasTemperateGrowth_deriv
-- name    : GlobalTheory.ExpDivision.hasTemperateGrowth_deriv
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:07:42.280357+00:00
-- url     : https://prove2.me/theorems/c2b82686-805d-497e-a1a8-4c1c39b4ac36
-- title:
--   Exp Division: has Temperate Growth deriv
-- statement:
--   The Exp Division construction uses the has Temperate Growth deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdentityAsSumExpMinusOne.lean#L20-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdentityAsSumExpMinusOne.lean#L20-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdentityAsSumExpMinusOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open GlobalTheory GlobalTheory.ExpDivision

theorem GlobalTheory.ExpDivision.hasTemperateGrowth_deriv {f : ℝ → ℂ} (hf : f.HasTemperateGrowth) :
    (deriv f).HasTemperateGrowth := by sorry
