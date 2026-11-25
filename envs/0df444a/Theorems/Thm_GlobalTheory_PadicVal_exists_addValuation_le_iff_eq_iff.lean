-- Prove2me | Theorems.Thm_GlobalTheory_PadicVal_exists_addValuation_le_iff_eq_iff
-- name    : GlobalTheory.PadicVal.exists_addValuation_le_iff_eq_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:14:56.776102+00:00
-- url     : https://prove2.me/theorems/9cb5981d-05ae-57df-9ca3-401551327c30
-- title:
--   Padic Val: exists add Valuation le iff eq iff
-- statement:
--   The Padic Val construction uses the exists add Valuation le iff eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsAddValuationLeIffEqIff.lean#L6-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsAddValuationLeIffEqIff.lean#L6-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsAddValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsAddValuationLeIffEqIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PadicVal

theorem GlobalTheory.PadicVal.exists_addValuation_le_iff_eq_iff : ∀ (p : ℕ) [Fact p.Prime] (π : PadicAlgCl p),
    0 < ‖π‖ → ‖π‖ < 1 → ∃ v : AddValuation (PadicAlgCl p) (WithTop ℚ),
      (∀ (c : PadicAlgCl p) (r : ℚ), (r : WithTop ℚ) ≤ v c ↔
        ‖c‖ ≤ Real.exp (-(-Real.log ‖π‖ * r))) ∧
      ∀ (c : PadicAlgCl p) (r : ℚ), v c = (r : WithTop ℚ) ↔
        ‖c‖ = Real.exp (-(-Real.log ‖π‖ * r)) := by sorry
