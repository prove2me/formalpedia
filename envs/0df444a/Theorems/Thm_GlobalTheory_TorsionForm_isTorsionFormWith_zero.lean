-- Prove2me | Theorems.Thm_GlobalTheory_TorsionForm_isTorsionFormWith_zero
-- name    : GlobalTheory.TorsionForm.isTorsionFormWith_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:42:08.370801+00:00
-- url     : https://prove2.me/theorems/d9debafe-8692-4e61-8a0a-a9d3787d6e8a
-- title:
--   Torsion Form: is Torsion Form With zero
-- statement:
--   The Torsion Form construction uses the is Torsion Form With zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/IsTorsionFormWithPoint.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/IsTorsionFormWithPoint.lean#L37-L39

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__TranslationInv_27ddeabb7aac02dc
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IsTorsionFormWithPoint_2137add7c40a5a9d
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff ComplexConjugate
open GlobalTheory GlobalTheory.TorsionForm
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g n : ℕ}
  (τ : E → Matrix (Fin g) (Fin g) ℂ) (M : Submodule ℤ (Fl g)) (j : Fl g → Pt E g → ℂ)
  (h : Pt E g → ℝ) (β : Fin n → E)

theorem GlobalTheory.TorsionForm.isTorsionFormWith_zero (b : E) (T : Ext (n + n)) :
    IsTorsionFormWith τ M j h β b 0 T ↔ IsTorsionForm τ M j h β b T := by sorry
