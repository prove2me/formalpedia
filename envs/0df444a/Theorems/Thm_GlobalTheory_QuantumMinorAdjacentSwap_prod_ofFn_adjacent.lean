-- Prove2me | Theorems.Thm_GlobalTheory_QuantumMinorAdjacentSwap_prod_ofFn_adjacent
-- name    : GlobalTheory.QuantumMinorAdjacentSwap.prod_ofFn_adjacent
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:13:30.720387+00:00
-- url     : https://prove2.me/theorems/1b445775-6c9c-4f99-82fb-364272107630
-- title:
--   Quantum Minor Adjacent Swap: prod of Fn adjacent
-- statement:
--   The Quantum Minor Adjacent Swap construction uses the prod of Fn adjacent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/QminorSwapAdjacent.lean#L24-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/QminorSwapAdjacent.lean#L24-L59

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_QminorSwapAdjacent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.QuantumMinorAdjacentSwap
variable {A : Type} [Ring A] [Algebra ℂ A]
omit [Algebra ℂ A]

theorem GlobalTheory.QuantumMinorAdjacentSwap.prod_ofFn_adjacent : ∀ (m : ℕ) (i : Fin m) (g₁ g₂ g₃ g₄ : Fin (m + 1) → A),
    (∀ k, k ≠ i.castSucc → k ≠ i.succ → g₂ k = g₁ k ∧ g₃ k = g₁ k ∧ g₄ k = g₁ k) →
    g₁ i.castSucc * g₁ i.succ + g₂ i.castSucc * g₂ i.succ =
      g₃ i.castSucc * g₃ i.succ + g₄ i.castSucc * g₄ i.succ →
    (List.ofFn g₁).prod + (List.ofFn g₂).prod = (List.ofFn g₃).prod + (List.ofFn g₄).prod
  := by sorry
