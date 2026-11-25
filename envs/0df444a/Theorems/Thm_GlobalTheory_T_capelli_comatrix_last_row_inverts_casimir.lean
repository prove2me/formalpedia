-- Prove2me | Theorems.Thm_GlobalTheory_T_capelli_comatrix_last_row_inverts_casimir
-- name    : GlobalTheory.T.capelli_comatrix_last_row_inverts_casimir
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:45:42.298852+00:00
-- url     : https://prove2.me/theorems/947d9723-2835-51f5-b721-d00cfa7d0ef0
-- title:
--   T: capelli comatrix last row inverts casimir
-- statement:
--   The T construction uses the capelli comatrix last row inverts casimir property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CapelliComatrixLastRowInvertsCasimirStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CapelliComatrixLastRowInvertsCasimirStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CapelliComatrixLastRowInvertsCasimir
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CapelliComatrixLastRowInvertsCasimirStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.capelli_comatrix_last_row_inverts_casimir : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (m : Fin (n + 1) → ℂ), GlRel E → (∀ w v, qdet E w v = (∏ j, (w + m j)) • v) → (∀ y b, Om y b = ∑ c, E c b (y c)) → ∃ K : ℂ → ((PiLp 2 (fun _ : Fin (n + 1) => V)) →ₗ[ℂ] V), (∀ u x, K u ((u - 0) • x + Om x) = (∏ j, (u + m j)) • x (Fin.last n)) ∧ ∀ u v, K u (PiLp.single 2 (Fin.last n) v) = qdet (fun a b : Fin n => E a.castSucc b.castSucc) (u - 1) v := by sorry
