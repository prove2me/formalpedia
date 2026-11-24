-- Prove2me | Theorems.Thm_GlobalTheory_JR_fourG_unitG
-- name    : GlobalTheory.JR.fourG_unitG
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:38:26.430922+00:00
-- url     : https://prove2.me/theorems/e4bff85e-af1f-4cc2-9d86-21f4dac050a8
-- title:
--   JR: four G unit G
-- statement:
--   The JR construction uses the four G unit G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PartialFourierGLBlockUnitIndicator.lean#L77-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PartialFourierGLBlockUnitIndicator.lean#L77-L124

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PartialFourierGLBlockUnitIndicator
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
open GlobalTheory GlobalTheory.JR
open FourGUnit

theorem GlobalTheory.JR.fourG_unitG : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ →
    fourG M ψ (unitG r F) = unitG r F := by sorry
