-- Prove2me | Theorems.Thm_GlobalTheory_NormUnits_norm_onto_units
-- name    : GlobalTheory.NormUnits.norm_onto_units
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T15:36:11.815806+00:00
-- url     : https://prove2.me/theorems/2eebdc61-c9bd-4f3d-9496-519c6bd52c52
-- title:
--   Norm Units: norm onto units
-- statement:
--   The Norm Units construction uses the norm onto units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsMulStarEqOfNormOneUnramifiedQuadratic.lean#L162-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsMulStarEqOfNormOneUnramifiedQuadratic.lean#L162-L276

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

theorem GlobalTheory.NormUnits.norm_onto_units : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (u : F), ‖u‖ = 1 → ∃ v : E, v * star v = algebraMap F E u := by sorry
