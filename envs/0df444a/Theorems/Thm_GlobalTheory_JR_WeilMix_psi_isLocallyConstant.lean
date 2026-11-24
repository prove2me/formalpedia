-- Prove2me | Theorems.Thm_GlobalTheory_JR_WeilMix_psi_isLocallyConstant
-- name    : GlobalTheory.JR.WeilMix.psi_isLocallyConstant
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:37:04.118456+00:00
-- url     : https://prove2.me/theorems/b5f14be8-590e-459c-afbe-40a74fa41234
-- title:
--   Weil Mix: psi is Locally Constant
-- statement:
--   The Weil Mix construction uses the psi is Locally Constant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocallyConstantCompactSupportMixedModelPartial.lean#L8-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocallyConstantCompactSupportMixedModelPartial.lean#L8-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantCompactSupportMixedModelPartial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilMix

theorem GlobalTheory.JR.WeilMix.psi_isLocallyConstant {F : Type} [NontriviallyNormedField F] (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) :
    IsLocallyConstant (fun x => ψ x) := by sorry
