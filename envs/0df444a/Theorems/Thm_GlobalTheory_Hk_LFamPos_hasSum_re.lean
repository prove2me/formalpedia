-- Prove2me | Theorems.Thm_GlobalTheory_Hk_LFamPos_hasSum_re
-- name    : GlobalTheory.Hk.LFamPos.hasSum_re
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:36:48.626634+00:00
-- url     : https://prove2.me/theorems/561965ec-fd43-4d20-ba44-197c433a4d59
-- title:
--   LFam Pos: has Sum re
-- statement:
--   The LFam Pos construction uses the has Sum re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassLFunctionFamilyLogDerivPositivity.lean#L22-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassLFunctionFamilyLogDerivPositivity.lean#L22-L40

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

theorem GlobalTheory.Hk.LFamPos.hasSum_re (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (σ : ℝ) (u : ℂ) (hs : 1 < σ) (hu : u.re = 0) :
    HasSum (fun n : ℕ => ∑ g, (if n = 0 then 0 else 𝓕.lam g n * (n : ℝ) ^ (-σ)) * (χ g * (n : ℂ) ^ (-u)).re)
      (LSeries (𝓕.lamChi χ) (σ + u)).re := by sorry
