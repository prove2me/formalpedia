-- Prove2me | Theorems.Thm_GlobalTheory_SBProd_exists_sum_box
-- name    : GlobalTheory.SBProd.exists_sum_box
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:32:26.758738+00:00
-- url     : https://prove2.me/theorems/656f0059-5137-4a53-9319-fb2029b13361
-- title:
--   SBProd: exists sum box
-- statement:
--   The SBProd construction uses the exists sum box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzProductDecomposition.lean#L34-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzProductDecomposition.lean#L34-L106

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzProductDecomposition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter Set
open scoped Classical
noncomputable section
open GlobalTheory GlobalTheory.SBProd

theorem GlobalTheory.SBProd.exists_sum_box (X : Type) [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] (κ κ' : Type) [Fintype κ] [Fintype κ'] (g : (κ ⊕ κ' → X) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (κ ⊕ κ' → X)) :
    ∃ (ι : Type) (_ : Fintype ι) (g₁ : ι → (κ → X) → ℂ) (g₂ : ι → (κ' → X) → ℂ),
      (∀ i, g₁ i ∈ GlobalTheory.WeilM.SB (κ → X)) ∧ (∀ i, g₂ i ∈ GlobalTheory.WeilM.SB (κ' → X)) ∧
      g = ∑ i, fun z => g₁ i (z ∘ Sum.inl) * g₂ i (z ∘ Sum.inr) := by sorry
