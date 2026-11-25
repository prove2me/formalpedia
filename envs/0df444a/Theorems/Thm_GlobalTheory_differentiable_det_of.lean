-- Prove2me | Theorems.Thm_GlobalTheory_differentiable_det_of
-- name    : GlobalTheory.differentiable_det_of
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:14:36.5975+00:00
-- url     : https://prove2.me/theorems/d27bdbc3-4d96-4f0f-b666-be47578a5d39
-- title:
--   Global Theory: differentiable det of
-- statement:
--   The Global Theory construction uses the differentiable det of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FrameSectionSliceEqPolyDivDetPow.lean#L8-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FrameSectionSliceEqPolyDivDetPow.lean#L8-L18

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_SemistableReduction_LatAll
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FrameSectionSliceEqPolyDivDetPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory

theorem GlobalTheory.differentiable_det_of {r : ℕ} :
    Differentiable ℂ (fun y : Fin r → Fin r → ℂ => (Matrix.of y).det) := by sorry
