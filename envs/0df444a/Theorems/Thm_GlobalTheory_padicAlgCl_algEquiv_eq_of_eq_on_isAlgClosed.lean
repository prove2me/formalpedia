-- Prove2me | Theorems.Thm_GlobalTheory_padicAlgCl_algEquiv_eq_of_eq_on_isAlgClosed
-- name    : GlobalTheory.padicAlgCl_algEquiv_eq_of_eq_on_isAlgClosed
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:49:38.684636+00:00
-- url     : https://prove2.me/theorems/0c73446e-d9fd-4920-a2f5-1ec720707fce
-- title:
--   Global Theory: padic Alg Cl alg Equiv eq of eq on is Alg Closed
-- statement:
--   The Global Theory construction uses the padic Alg Cl alg Equiv eq of eq on is Alg Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PadicAutomorphismUnique.lean#L38-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PadicAutomorphismUnique.lean#L38-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicAutomorphismUnique
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

theorem GlobalTheory.padicAlgCl_algEquiv_eq_of_eq_on_isAlgClosed :
    ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [IsAlgClosed Ω] (j : Ω →+* PadicAlgCl l)
      (σ τ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l), (∀ x, σ (j x) = τ (j x)) → σ = τ := by sorry
