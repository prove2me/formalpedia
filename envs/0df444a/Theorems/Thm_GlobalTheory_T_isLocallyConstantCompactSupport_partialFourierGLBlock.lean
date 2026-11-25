-- Prove2me | Theorems.Thm_GlobalTheory_T_isLocallyConstantCompactSupport_partialFourierGLBlock
-- name    : GlobalTheory.T.isLocallyConstantCompactSupport_partialFourierGLBlock
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:36:17.032247+00:00
-- url     : https://prove2.me/theorems/7a61a1ae-2a0a-5d12-9bd1-7bf493a58c73
-- title:
--   T: is Locally Constant Compact Support partial Fourier GLBlock
-- statement:
--   The T construction uses the is Locally Constant Compact Support partial Fourier GLBlock property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocallyConstantCompactSupportPartialFourierGLBStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocallyConstantCompactSupportPartialFourierGLBStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantCompactSupportPartialFourierGLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantCompactSupportPartialFourierGLBStatement
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

theorem GlobalTheory.T.isLocallyConstantCompactSupport_partialFourierGLBlock : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ f' : Gl r F → ℂ, IsTest f' → IsTest (fourG M ψ f') := by sorry
