-- Prove2me | Theorems.Thm_GlobalTheory_JR_WeilProd_TensorTest_isTest_mul_prod
-- name    : GlobalTheory.JR.WeilProd.TensorTest.isTest_mul_prod
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:37:28.2267+00:00
-- url     : https://prove2.me/theorems/6790407b-aea2-40b8-a703-6c51438a42ba
-- title:
--   Tensor Test: is Test mul prod
-- statement:
--   The Tensor Test construction uses the is Test mul prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocallyConstantTestRepresentationTensorProduct.lean#L61-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocallyConstantTestRepresentationTensorProduct.lean#L61-L69

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

theorem GlobalTheory.JR.WeilProd.TensorTest.isTest_mul_prod {a : X → ℂ} {b : Y → ℂ} (ha : IsTest a) (hb : IsTest b) :
    IsTest (fun p : X × Y => a p.1 * b p.2) := by sorry
