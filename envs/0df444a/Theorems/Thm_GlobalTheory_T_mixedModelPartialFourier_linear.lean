-- Prove2me | Theorems.Thm_GlobalTheory_T_mixedModelPartialFourier_linear
-- name    : GlobalTheory.T.mixedModelPartialFourier_linear
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:52:59.022031+00:00
-- url     : https://prove2.me/theorems/8d5a782a-b696-4539-a976-92d6e02d71e3
-- title:
--   T: mixed Model Partial Fourier linear
-- statement:
--   The T construction uses the mixed Model Partial Fourier linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MixedModelPartialFourierLinearStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MixedModelPartialFourierLinearStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MixedModelPartialFourierLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MixedModelPartialFourierLinearStatement
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

theorem GlobalTheory.T.mixedModelPartialFourier_linear : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (c : ℂ) (f f' : Gl r F → ℂ), IsTest f → IsTest f' → WeilMix.ptrB M ψ (c • f + f') = c • WeilMix.ptrB M ψ f + WeilMix.ptrB M ψ f' := by sorry
