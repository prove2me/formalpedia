-- Prove2me | Theorems.Thm_GlobalTheory_Hk_LFamPos_w_nonneg
-- name    : GlobalTheory.Hk.LFamPos.w_nonneg
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:21:28.048945+00:00
-- url     : https://prove2.me/theorems/75c062bd-f654-4e25-9f66-1fc490706e90
-- title:
--   LFam Pos: w nonneg
-- statement:
--   The LFam Pos construction uses the w nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassLFunctionFamilyLogDerivPositivity.lean#L47-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassLFunctionFamilyLogDerivPositivity.lean#L47-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyLogDerivPositivity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.LFamPos

theorem GlobalTheory.Hk.LFamPos.w_nonneg (𝓕 : LFam) (σ : ℝ) (n : ℕ) (g : 𝓕.G) :
    0 ≤ (if n = 0 then 0 else 𝓕.lam g n * (n : ℝ) ^ (-σ)) := by sorry
