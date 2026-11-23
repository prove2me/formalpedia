-- Prove2me | Theorems.Thm_GlobalTheory_JR_WeilProd_TensorTest_isTest_smul
-- name    : GlobalTheory.JR.WeilProd.TensorTest.isTest_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:52:54.767815+00:00
-- url     : https://prove2.me/theorems/adbda5fc-ed2e-438a-8f6d-f25e0a4de1b7
-- title:
--   Tensor Test: is Test smul
-- statement:
--   The Tensor Test construction uses the is Test smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocallyConstantTestRepresentationTensorProduct.lean#L27-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocallyConstantTestRepresentationTensorProduct.lean#L27-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TensorRepApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantTestRepresentationTensorProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilProd Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilProd GlobalTheory.JR.WeilProd.TensorTest
variable {X : Type} [TopologicalSpace X]

theorem GlobalTheory.JR.WeilProd.TensorTest.isTest_smul (c : ℂ) {f : X → ℂ} (hf : IsTest f) : IsTest (c • f) := by sorry
