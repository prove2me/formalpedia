-- Prove2me | Theorems.Thm_GlobalTheory_eigencharacters_finite_of_commuting_annihilated
-- name    : GlobalTheory.eigencharacters_finite_of_commuting_annihilated
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:16:35.948798+00:00
-- url     : https://prove2.me/theorems/0d743c69-6a01-4808-abd1-a2934e87a68c
-- title:
--   Global Theory: eigencharacters finite of commuting annihilated
-- statement:
--   The Global Theory construction uses the eigencharacters finite of commuting annihilated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EigencharactersFiniteOfCommutingAnnihilated.lean#L7-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EigencharactersFiniteOfCommutingAnnihilated.lean#L7-L88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EigencharactersFiniteOfCommutingAnnihilated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial

theorem GlobalTheory.eigencharacters_finite_of_commuting_annihilated :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (T : Finset (Module.End ℂ V))
      (p : Module.End ℂ V → Polynomial ℂ), (∀ s ∈ T, ∀ t ∈ T, Commute s t) →
      (∀ t ∈ T, p t ≠ 0) → ∃ X' : Set (Module.End ℂ V → ℂ), X'.Finite ∧ ∀ ψ : V,
        (∀ t ∈ T, Polynomial.aeval t (p t) ψ = 0) → ∀ (χ' : Module.End ℂ V → ℂ) (u : V),
        u ∈ Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) ''
          (Algebra.adjoin ℂ (T : Set (Module.End ℂ V)) : Set (Module.End ℂ V))) → u ≠ 0 →
        (∀ z ∈ Algebra.adjoin ℂ (T : Set (Module.End ℂ V)), z u = χ' z • u) →
        ∃ χ ∈ X', ∀ z ∈ Algebra.adjoin ℂ (T : Set (Module.End ℂ V)), χ' z = χ z := by sorry
