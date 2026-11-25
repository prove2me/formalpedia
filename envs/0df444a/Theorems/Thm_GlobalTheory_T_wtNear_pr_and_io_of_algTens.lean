-- Prove2me | Theorems.Thm_GlobalTheory_T_wtNear_pr_and_io_of_algTens
-- name    : GlobalTheory.T.wtNear_pr_and_io_of_algTens
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:35:37.4009+00:00
-- url     : https://prove2.me/theorems/bd43382e-3060-47b1-9f79-d10bd2d45f58
-- title:
--   T: wt Near pr and io of alg Tens
-- statement:
--   The T construction uses the wt Near pr and io of alg Tens property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/AlgTensWtNearStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/AlgTensWtNearStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_AlgTensWtNear
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_AlgTensWtNearStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.wtNear_pr_and_io_of_algTens : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (Λ : Fin n → ℝ) (t : ℝ), AlgTens ε E N F io pr → (∀ w, w ∈ WtNear E Λ t → ∀ s c, pr s (Pi.single c w) ∈ WtNear (F s) Λ (t + 1)) ∧ ∀ s (y : N s), y ∈ WtNear (F s) Λ t → ∀ d, io s y d ∈ WtNear E Λ (t + 1) := by sorry
