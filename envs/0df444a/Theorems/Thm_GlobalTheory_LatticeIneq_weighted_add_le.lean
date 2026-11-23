-- Prove2me | Theorems.Thm_GlobalTheory_LatticeIneq_weighted_add_le
-- name    : GlobalTheory.LatticeIneq.weighted_add_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:11:33.158749+00:00
-- url     : https://prove2.me/theorems/2393e5c0-146c-4ca4-80f4-534d4fd8bc44
-- title:
--   Lattice Ineq: weighted add le
-- statement:
--   The Lattice Ineq construction uses the weighted add le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsReducedCombination.lean#L11-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsReducedCombination.lean#L11-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsReducedCombination
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory
open GlobalTheory.LatticeIneq
variable {X : Type} [AddCommGroup X]

theorem GlobalTheory.LatticeIneq.weighted_add_le (q : QuadraticMap ℤ X ℝ) (hq : ∀ x, 0 ≤ q x) (j : ℕ) (a b : X) :
    (j : ℝ) * q (a + b) ≤ (j + 1) * q a + j * (j + 1) * q b := by sorry
