-- Prove2me | Theorems.Thm_GlobalTheory_exists_inner_dual_basis
-- name    : GlobalTheory.exists_inner_dual_basis
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:02:00.383589+00:00
-- url     : https://prove2.me/theorems/80dbae6f-eb90-47ff-82d4-b74816fb0a2b
-- title:
--   Global Theory: exists inner dual basis
-- statement:
--   The Global Theory construction uses the exists inner dual basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/ExistsBasisSpanEqOfDiscrete.lean#L22-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/ExistsBasisSpanEqOfDiscrete.lean#L22-L34

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Transference
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_ExistsBasisSpanEqOfDiscrete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
open GlobalTheory

theorem GlobalTheory.exists_inner_dual_basis {N : ℕ} (b : Basis (Fin N) ℝ (EuclideanSpace ℝ (Fin N))) :
    ∃ d : Basis (Fin N) ℝ (EuclideanSpace ℝ (Fin N)), ∀ j y, inner ℝ (d j) y = b.repr y j := by sorry
