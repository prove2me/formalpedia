-- Prove2me | Theorems.Thm_GlobalTheory_JR_WeilProd_TensorTest_isTest_fibre
-- name    : GlobalTheory.JR.WeilProd.TensorTest.isTest_fibre
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:52:43.056834+00:00
-- url     : https://prove2.me/theorems/e37e7ad5-e05b-4a1a-ac42-60a639f6eabf
-- title:
--   Tensor Test: is Test fibre
-- statement:
--   The Tensor Test construction uses the is Test fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocallyConstantTestRepresentationTensorProduct.lean#L71-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocallyConstantTestRepresentationTensorProduct.lean#L71-L74

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
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem GlobalTheory.JR.WeilProd.TensorTest.isTest_fibre {f : X × Y → ℂ} (hf : IsTest f) (u : X) : IsTest (fun v => f (u, v)) := by sorry
