-- Prove2me | Theorems.Thm_GlobalTheory_JR_WeilProd_TensorTest_decomp
-- name    : GlobalTheory.JR.WeilProd.TensorTest.decomp
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:37:21.638165+00:00
-- url     : https://prove2.me/theorems/c88ee6f4-207c-4034-98ce-8b598c416e5e
-- title:
--   Tensor Test: decomp
-- statement:
--   The Tensor Test construction uses the decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocallyConstantTestRepresentationTensorProduct.lean#L104-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocallyConstantTestRepresentationTensorProduct.lean#L104-L144

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

theorem GlobalTheory.JR.WeilProd.TensorTest.decomp {f : X × Y → ℂ} (hf : IsTest f) :
    ∃ (s : Finset (Y → ℂ)) (a : (Y → ℂ) → X → ℂ), (∀ φ ∈ s, IsTest (a φ)) ∧ (∀ φ ∈ s, IsTest φ) ∧
      ∀ p : X × Y, f p = ∑ φ ∈ s, a φ p.1 * φ p.2 := by sorry
