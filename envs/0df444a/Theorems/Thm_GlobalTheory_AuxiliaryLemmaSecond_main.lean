-- Prove2me | Theorems.Thm_GlobalTheory_AuxiliaryLemmaSecond_main
-- name    : GlobalTheory.AuxiliaryLemmaSecond.main
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:56:43.008018+00:00
-- url     : https://prove2.me/theorems/72011538-1345-4faa-88f0-b0c7d0ae2ed7
-- title:
--   Auxiliary Lemma Second: main
-- statement:
--   The Auxiliary Lemma Second construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ImportsMoreTail.lean#L7-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ImportsMoreTail.lean#L7-L77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsMoreTail
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AuxiliaryLemmaSecond
open IsLocalRing

theorem GlobalTheory.AuxiliaryLemmaSecond.main : ∀ {κ : Type} [inst : Field κ] (R : Subring κ) [IsNoetherianRing ↥R] [IsIntegrallyClosed ↥R]
    [IsFractionRing (↥R) κ] (Q : Ideal ↥R) [Ideal.IsPrime Q], Q ≠ ⊥ →
    (∀ (p : Ideal ↥R), Ideal.IsPrime p → p ≠ ⊥ → p ≤ Q → p = Q) →
    ∃ (W : ValuationSubring κ), IsDiscreteValuationRing ↥W ∧ (∀ (r : ↥R), (↑r : κ) ∈ W) ∧
      (∀ r ∉ Q, (↑r : κ)⁻¹ ∈ W) ∧ (∀ r ∈ Q, r ≠ (0 : ↥R) → (↑r : κ)⁻¹ ∉ W) ∧
      ∀ w ∈ W, ∃ (b : ↥R), ∃ s ∉ Q, w = (↑b : κ) / (↑s : κ) := by sorry
