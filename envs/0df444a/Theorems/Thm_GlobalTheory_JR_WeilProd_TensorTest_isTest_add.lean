-- Prove2me | Theorems.Thm_GlobalTheory_JR_WeilProd_TensorTest_isTest_add
-- name    : GlobalTheory.JR.WeilProd.TensorTest.isTest_add
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:36:55.124839+00:00
-- url     : https://prove2.me/theorems/9a15c1ca-562c-4929-9281-508dae02e489
-- title:
--   Tensor Test: is Test add
-- statement:
--   The Tensor Test construction uses the is Test add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocallyConstantTestRepresentationTensorProduct.lean#L24-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocallyConstantTestRepresentationTensorProduct.lean#L24-L25

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

theorem GlobalTheory.JR.WeilProd.TensorTest.isTest_add {f f' : X → ℂ} (hf : IsTest f) (hf' : IsTest f') : IsTest (f + f') := by sorry
