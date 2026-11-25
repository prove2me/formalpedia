-- Prove2me | Theorems.Thm_GlobalTheory_T_schwartz_product_decomposition
-- name    : GlobalTheory.T.schwartz_product_decomposition
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:37:20.101067+00:00
-- url     : https://prove2.me/theorems/57f3b15f-a794-485a-bfe5-b291724fa43b
-- title:
--   T: schwartz product decomposition
-- statement:
--   The T construction uses the schwartz product decomposition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzProductDecompositionStatement.lean#L6-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzProductDecompositionStatement.lean#L6-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzProductDecomposition
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzProductDecompositionStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.schwartz_product_decomposition : ∀ (X : Type) [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    (κ κ' : Type) [Fintype κ] [Fintype κ'] (g : (κ ⊕ κ' → X) → ℂ), g ∈ GlobalTheory.WeilM.SB (κ ⊕ κ' → X) →
    ∃ (ι : Type) (_ : Fintype ι) (g₁ : ι → (κ → X) → ℂ) (g₂ : ι → (κ' → X) → ℂ),
      (∀ i, g₁ i ∈ GlobalTheory.WeilM.SB (κ → X)) ∧ (∀ i, g₂ i ∈ GlobalTheory.WeilM.SB (κ' → X)) ∧
      g = ∑ i, fun z => g₁ i (z ∘ Sum.inl) * g₂ i (z ∘ Sum.inr) := by sorry
