-- Prove2me | Theorems.Thm_GlobalTheory_JR_exists_nhds_zero_add_invariant_of_isTest
-- name    : GlobalTheory.JR.exists_nhds_zero_add_invariant_of_isTest
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:39:08.41213+00:00
-- url     : https://prove2.me/theorems/8a2a0d67-768d-4b0e-aa7c-15c2c00e5c4e
-- title:
--   JR: exists nhds zero add invariant of is Test
-- statement:
--   The JR construction uses the exists nhds zero add invariant of is Test property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocallyConstantCompactSupportPartialFourierGLB.lean#L10-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocallyConstantCompactSupportPartialFourierGLB.lean#L10-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantPartialFourierGLBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HasCompactSupportPartialFourierGLBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantCompactSupportPartialFourierGLB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR

theorem GlobalTheory.JR.exists_nhds_zero_add_invariant_of_isTest {X : Type} [UniformSpace X] [AddCommGroup X] [IsUniformAddGroup X] {f : X → ℂ}
    (hf : IsTest f) : ∃ U ∈ 𝓝 (0 : X), ∀ Y : X, ∀ u ∈ U, f (Y + u) = f Y := by sorry
