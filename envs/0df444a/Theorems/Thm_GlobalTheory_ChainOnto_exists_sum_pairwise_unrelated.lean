-- Prove2me | Theorems.Thm_GlobalTheory_ChainOnto_exists_sum_pairwise_unrelated
-- name    : GlobalTheory.ChainOnto.exists_sum_pairwise_unrelated
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:20:30.423854+00:00
-- url     : https://prove2.me/theorems/1efe1fc0-aeb3-5689-bc5b-4c98f269c4d1
-- title:
--   Chain Onto: exists sum pairwise unrelated
-- statement:
--   The Chain Onto construction uses the exists sum pairwise unrelated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SurjectiveOfAdjointSeparatesLabelledParts.lean#L7-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SurjectiveOfAdjointSeparatesLabelledParts.lean#L7-L83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SurjectiveOfAdjointSeparatesLabelledParts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.ChainOnto

theorem GlobalTheory.ChainOnto.exists_sum_pairwise_unrelated {A I : Type} [AddCommGroup A] [Module ℂ A]
    (pA : A → I → Prop) (RA : I → I → Prop) (hRA : Equivalence RA)
    (hmerge : ∀ u u' B B' (a : ℂ), pA u B → pA u' B' → RA B B' → u + a • u' ≠ 0 → pA (u + a • u') B)
    (hsmul : ∀ u B (a : ℂ), pA u B → a ≠ 0 → pA (a • u) B) (u : A)
    (hu : u ∈ Submodule.span ℂ {u | ∃ B, pA u B}) :
    ∃ (s : Finset I) (v : I → A), (∀ i ∈ s, pA (v i) i) ∧
      (∀ i ∈ s, ∀ i' ∈ s, i ≠ i' → ¬ RA i i') ∧ u = ∑ i ∈ s, v i := by sorry
