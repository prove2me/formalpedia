-- Prove2me | Theorems.Thm_GlobalTheory_JR_WeilProd_TensorTest_tensorRep_eq
-- name    : GlobalTheory.JR.WeilProd.TensorTest.tensorRep_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:36:46.255209+00:00
-- url     : https://prove2.me/theorems/87eddc9e-7c3e-4149-a909-4a4b9b67ed09
-- title:
--   Tensor Test: tensor Rep eq
-- statement:
--   The Tensor Test construction uses the tensor Rep eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocallyConstantTestRepresentationTensorProduct.lean#L146-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocallyConstantTestRepresentationTensorProduct.lean#L146-L161

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

theorem GlobalTheory.JR.WeilProd.TensorTest.tensorRep_eq {G H : Type} [Group G] [Group H] {W₁ : G → (X → ℂ) → X → ℂ}
    {W₂ : H → (Y → ℂ) → Y → ℂ} (hW₁ : IsTestRep W₁) (hW₂ : IsTestRep W₂) {ι : Type} (s : Finset ι)
    (A : ι → X → ℂ) (B : ι → Y → ℂ) (hA : ∀ j ∈ s, IsTest (A j)) (hB : ∀ j ∈ s, IsTest (B j))
    (f : X × Y → ℂ) (hf : ∀ p : X × Y, f p = ∑ j ∈ s, A j p.1 * B j p.2) (gh : G × H) :
    tensorRep W₁ W₂ gh f = fun p => ∑ j ∈ s, W₁ gh.1 (A j) p.1 * W₂ gh.2 (B j) p.2 := by sorry
