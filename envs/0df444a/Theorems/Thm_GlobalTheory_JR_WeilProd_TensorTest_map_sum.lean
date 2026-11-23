-- Prove2me | Theorems.Thm_GlobalTheory_JR_WeilProd_TensorTest_map_sum
-- name    : GlobalTheory.JR.WeilProd.TensorTest.map_sum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:52:57.507304+00:00
-- url     : https://prove2.me/theorems/50d5d30c-2e97-4021-8e28-4fda20090801
-- title:
--   Tensor Test: map sum
-- statement:
--   The Tensor Test construction uses the map sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocallyConstantTestRepresentationTensorProduct.lean#L43-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocallyConstantTestRepresentationTensorProduct.lean#L43-L54

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

theorem GlobalTheory.JR.WeilProd.TensorTest.map_sum {G : Type} [Group G] {W : G → (X → ℂ) → X → ℂ} (hW : IsTestRep W) (g : G) {ι : Type}
    (s : Finset ι) (c : ι → ℂ) (f : ι → X → ℂ) (hf : ∀ j ∈ s, IsTest (f j)) :
    W g (∑ j ∈ s, c j • f j) = ∑ j ∈ s, c j • W g (f j) := by sorry
