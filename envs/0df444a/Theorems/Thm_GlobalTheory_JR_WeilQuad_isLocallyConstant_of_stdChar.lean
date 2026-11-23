-- Prove2me | Theorems.Thm_GlobalTheory_JR_WeilQuad_isLocallyConstant_of_stdChar
-- name    : GlobalTheory.JR.WeilQuad.isLocallyConstant_of_stdChar
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:53:33.373072+00:00
-- url     : https://prove2.me/theorems/d306b91b-7b89-46af-b30f-fa8e67307672
-- title:
--   Weil Quad: is Locally Constant of std Char
-- statement:
--   The Weil Quad construction uses the is Locally Constant of std Char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/QuadraticWeilUnipotentTorusPreserveTest.lean#L13-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/QuadraticWeilUnipotentTorusPreserveTest.lean#L13-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilUnipotentTorusPreserveTest
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilQuad
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem GlobalTheory.JR.WeilQuad.isLocallyConstant_of_stdChar {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) : IsLocallyConstant ψ := by sorry
