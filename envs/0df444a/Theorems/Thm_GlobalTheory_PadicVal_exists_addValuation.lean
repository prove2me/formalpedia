-- Prove2me | Theorems.Thm_GlobalTheory_PadicVal_exists_addValuation
-- name    : GlobalTheory.PadicVal.exists_addValuation
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:41:52.995578+00:00
-- url     : https://prove2.me/theorems/d3d68782-0bc9-458a-81c8-27b103559b78
-- title:
--   Padic Val: exists add Valuation
-- statement:
--   The Padic Val construction uses the exists add Valuation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsAddValuation.lean#L20-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsAddValuation.lean#L20-L93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsAddValuation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PadicVal
variable {p : ℕ} [Fact p.Prime]
open Classical

theorem GlobalTheory.PadicVal.exists_addValuation (π : PadicAlgCl p) (h0 : 0 < ‖π‖) (h1 : ‖π‖ < 1) :
    ∃ v : AddValuation (PadicAlgCl p) (WithTop ℚ), ∀ x, x ≠ 0 →
      ∃ q : ℚ, v x = (q : WithTop ℚ) ∧ Real.log ‖x‖ = q * Real.log ‖π‖ := by sorry
