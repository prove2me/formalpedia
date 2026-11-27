-- Prove2me | Theorems.Thm_GlobalTheory_TorsionForm_wedge_contr_add
-- name    : GlobalTheory.TorsionForm.wedge_contr_add
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:42:01.011965+00:00
-- url     : https://prove2.me/theorems/8d78de79-5bc1-447d-82c0-64355c0f94ad
-- title:
--   Torsion Form: wedge contr add
-- statement:
--   The Torsion Form construction uses the wedge contr add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/IsTorsionFormPoint.lean#L126-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/IsTorsionFormPoint.lean#L126-L131

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_SiegelReframe
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IsTorsionFormPoint_049da9a0b6d9fde7
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
open scoped Real ContDiff
open GlobalTheory GlobalTheory.TorsionForm
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g n : ℕ}
  (τ : E → Matrix (Fin g) (Fin g) ℂ) (M : Submodule ℤ (Fl g)) (j : Fl g → Pt E g → ℂ)
  (h : Pt E g → ℝ) (β : Fin n → E)

theorem GlobalTheory.TorsionForm.wedge_contr_add {m : ℕ} (i : Fin m) (w : Ext m) :
    wedge i (contr i w) + contr i (wedge i w) = w := by sorry
