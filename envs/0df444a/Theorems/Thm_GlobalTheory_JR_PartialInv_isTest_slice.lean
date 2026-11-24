-- Prove2me | Theorems.Thm_GlobalTheory_JR_PartialInv_isTest_slice
-- name    : GlobalTheory.JR.PartialInv.isTest_slice
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:34:20.679751+00:00
-- url     : https://prove2.me/theorems/5069174c-d8dd-4eba-a5e0-aa2efe8ab2e4
-- title:
--   Partial Inv: is Test slice
-- statement:
--   The Partial Inv construction uses the is Test slice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MixedModelPartialFourierColumnTwiceNegColumn.lean#L31-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MixedModelPartialFourierColumnTwiceNegColumn.lean#L31-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MixedModelPartialFourierColumnTwiceNegColumn
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
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.PartialInv

theorem GlobalTheory.JR.PartialInv.isTest_slice {F : Type} [NormedField F] {r : ℕ} {f : Gl r F → ℂ} (hf : IsTest f)
    (A : Matrix (Fin r) (Fin r) F) (c : Fin r → F) (l : F) : IsTest fun v : Fin r → F => f (A, v, c, l) := by sorry
