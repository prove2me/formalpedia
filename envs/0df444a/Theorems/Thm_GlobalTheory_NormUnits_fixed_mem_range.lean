-- Prove2me | Theorems.Thm_GlobalTheory_NormUnits_fixed_mem_range
-- name    : GlobalTheory.NormUnits.fixed_mem_range
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T15:36:42.271145+00:00
-- url     : https://prove2.me/theorems/1550fdc5-b7af-436a-89c9-daeedbe3f0f1
-- title:
--   Norm Units: fixed mem range
-- statement:
--   The Norm Units construction uses the fixed mem range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsMulStarEqOfNormOneUnramifiedQuadratic.lean#L70-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsMulStarEqOfNormOneUnramifiedQuadratic.lean#L70-L109

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TotalDegreeCMulXMulX
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMulStarEqOfNormOneUnramifiedQuadratic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.NormUnits

theorem GlobalTheory.NormUnits.fixed_mem_range (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [hU : Unram F E] (ζ : E) (hζ : ∀ b : F, 1 ≤ ‖ζ - algebraMap F E b‖) :
    ∀ w : E, star w = w → ∃ a : F, algebraMap F E a = w := by sorry
