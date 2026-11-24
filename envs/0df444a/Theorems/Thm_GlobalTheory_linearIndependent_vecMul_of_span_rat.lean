-- Prove2me | Theorems.Thm_GlobalTheory_linearIndependent_vecMul_of_span_rat
-- name    : GlobalTheory.linearIndependent_vecMul_of_span_rat
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:07:09.266186+00:00
-- url     : https://prove2.me/theorems/97868139-b9ec-49ba-9521-add60f31d43e
-- title:
--   Global Theory: linear Independent vec Mul of span rat
-- statement:
--   The Global Theory construction uses the linear Independent vec Mul of span rat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LinearIndependentVecMulOfSpanRat.lean#L7-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LinearIndependentVecMulOfSpanRat.lean#L7-L70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LinearIndependentVecMulOfSpanRat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open NumberField IsDedekindDomain
open GlobalTheory

theorem GlobalTheory.linearIndependent_vecMul_of_span_rat :
    ∀ (E : Type) [Field E] [NumberField E] (R : Type) [CommRing R] [Algebra ℝ R] [FiniteDimensional ℝ R] (τ : E →+* R), Submodule.span ℝ (Set.range τ) = ⊤ → Module.finrank ℝ R = Module.finrank ℚ E → ∀ (n : ℕ) (ι : Type) [Fintype ι] (u : ι → Fin n → E), Fintype.card ι = Module.finrank ℚ E * n → Submodule.span ℚ (Set.range u) = ⊤ → ∀ g : GL (Fin n) R, LinearIndependent ℝ fun k => (fun i => τ (u k i)) ᵥ* g.1 := by sorry
