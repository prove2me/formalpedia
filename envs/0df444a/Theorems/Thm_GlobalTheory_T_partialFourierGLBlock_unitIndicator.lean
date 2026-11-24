-- Prove2me | Theorems.Thm_GlobalTheory_T_partialFourierGLBlock_unitIndicator
-- name    : GlobalTheory.T.partialFourierGLBlock_unitIndicator
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:55:34.531841+00:00
-- url     : https://prove2.me/theorems/166f9386-ad51-48b4-83f4-50eeb9c72c66
-- title:
--   T: partial Fourier GLBlock unit Indicator
-- statement:
--   The T construction uses the partial Fourier GLBlock unit Indicator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PartialFourierGLBlockUnitIndicatorStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PartialFourierGLBlockUnitIndicatorStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PartialFourierGLBlockUnitIndicator
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PartialFourierGLBlockUnitIndicatorStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.partialFourierGLBlock_unitIndicator : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → fourG M ψ (unitG r F) = unitG r F := by sorry
