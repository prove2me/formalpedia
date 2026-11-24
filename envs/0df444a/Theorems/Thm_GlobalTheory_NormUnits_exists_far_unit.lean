-- Prove2me | Theorems.Thm_GlobalTheory_NormUnits_exists_far_unit
-- name    : GlobalTheory.NormUnits.exists_far_unit
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T15:36:08.466744+00:00
-- url     : https://prove2.me/theorems/f2a2c428-ebf8-42fb-b759-25d9288b355e
-- title:
--   Norm Units: exists far unit
-- statement:
--   The Norm Units construction uses the exists far unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsMulStarEqOfNormOneUnramifiedQuadratic.lean#L26-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsMulStarEqOfNormOneUnramifiedQuadratic.lean#L26-L64

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

theorem GlobalTheory.NormUnits.exists_far_unit (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [hU : Unram F E] :
    ∃ ζ : E, ‖ζ‖ = 1 ∧ ∀ b : F, 1 ≤ ‖ζ - algebraMap F E b‖ := by sorry
