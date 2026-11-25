-- Prove2me | Theorems.Thm_GlobalTheory_wtNear_le_of_add_dist_le
-- name    : GlobalTheory.wtNear_le_of_add_dist_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:23:25.895878+00:00
-- url     : https://prove2.me/theorems/f844a13b-d128-4b23-991d-ce706ca8c395
-- title:
--   Global Theory: wt Near le of add dist le
-- statement:
--   The Global Theory construction uses the wt Near le of add dist le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/WtNearLeOfAddDistLe.lean#L9-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/WtNearLeOfAddDistLe.lean#L9-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_WtNearLeOfAddDistLe
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
open GlobalTheory

theorem GlobalTheory.wtNear_le_of_add_dist_le :
    ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool)
      (E : Fin n → Fin n → Module.End ℂ M) (Λ Λ' : Fin n → ℝ) (t t' : ℝ),
      t + ∑ a, |Λ a - Λ' a| ≤ t' → WtNear E Λ t ≤ WtNear E Λ' t' := by sorry
