-- Prove2me | Theorems.Thm_GlobalTheory_T_isLocallyConstantCompactSupport_mixedModelPartialFourierColumn
-- name    : GlobalTheory.T.isLocallyConstantCompactSupport_mixedModelPartialFourierColumn
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:49:02.758806+00:00
-- url     : https://prove2.me/theorems/f3470d75-68db-4bef-a2ca-4d9a74a640a1
-- title:
--   T: is Locally Constant Compact Support mixed Model Partial Fourier Column
-- statement:
--   The T construction uses the is Locally Constant Compact Support mixed Model Partial Fourier Column property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocallyConstantCompactSupportMixedModelPartialStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocallyConstantCompactSupportMixedModelPartialStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantCompactSupportMixedModelPartial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantCompactSupportMixedModelPartialStatement
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

theorem GlobalTheory.T.isLocallyConstantCompactSupport_mixedModelPartialFourierColumn : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ f : Gl r F → ℂ, IsTest f → IsTest (WeilMix.ptrB M ψ f) := by sorry
