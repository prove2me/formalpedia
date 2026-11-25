-- Prove2me | Theorems.Thm_GlobalTheory_lastComatrixRow_inverts_dual
-- name    : GlobalTheory.lastComatrixRow_inverts_dual
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:53:58.119334+00:00
-- url     : https://prove2.me/theorems/8bd7eef9-8ccb-4a21-9482-08997f54e46c
-- title:
--   Global Theory: last Comatrix Row inverts dual
-- statement:
--   The Global Theory construction uses the last Comatrix Row inverts dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/LastComatrixRowInvertsDual.lean#L7-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/LastComatrixRowInvertsDual.lean#L7-L40

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_LastComatrixRowInvertsDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL
open GlobalTheory

theorem GlobalTheory.lastComatrixRow_inverts_dual : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (m : Fin (n + 1) → ℂ), _root_.Formalism.REAL.GlRel E → (∀ w v, _root_.Formalism.REAL.qdet E w v = (∏ j, (w + m j)) • v) → (∀ y a, Om y a = ∑ c, E a c (y c)) → ∃ K : ℂ → ((PiLp 2 (fun _ : Fin (n + 1) => V)) →ₗ[ℂ] V), (∀ u x, K u ((u - (n : ℂ)) • x + Om x) = (∏ j, (u + m j)) • x (Fin.last n)) ∧ ∀ u v, K u (PiLp.single 2 (Fin.last n) v) = _root_.Formalism.REAL.qdet (fun a b : Fin n => E a.castSucc b.castSucc) u v := by sorry
