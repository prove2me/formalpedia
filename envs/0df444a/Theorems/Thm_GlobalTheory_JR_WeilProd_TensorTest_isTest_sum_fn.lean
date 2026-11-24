-- Prove2me | Theorems.Thm_GlobalTheory_JR_WeilProd_TensorTest_isTest_sum_fn
-- name    : GlobalTheory.JR.WeilProd.TensorTest.isTest_sum_fn
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:36:42.909647+00:00
-- url     : https://prove2.me/theorems/da9ae552-d78a-4fe9-b026-d1604e19a2a8
-- title:
--   Tensor Test: is Test sum fn
-- statement:
--   The Tensor Test construction uses the is Test sum fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocallyConstantTestRepresentationTensorProduct.lean#L99-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocallyConstantTestRepresentationTensorProduct.lean#L99-L102

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

theorem GlobalTheory.JR.WeilProd.TensorTest.isTest_sum_fn {ι : Type} (s : Finset ι) (F : ι → X × Y → ℂ) (hF : ∀ j ∈ s, IsTest (F j)) :
    IsTest (fun p => ∑ j ∈ s, F j p) := by sorry
