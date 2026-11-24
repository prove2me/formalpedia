-- Prove2me | Theorems.Thm_GlobalTheory_LatticeIneq_map_sum_le
-- name    : GlobalTheory.LatticeIneq.map_sum_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:00:21.052161+00:00
-- url     : https://prove2.me/theorems/32c5561e-cacf-4398-8e19-26271cbb4c8f
-- title:
--   Lattice Ineq: map sum le
-- statement:
--   The Lattice Ineq construction uses the map sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsReducedCombination.lean#L26-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsReducedCombination.lean#L26-L41

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

theorem GlobalTheory.LatticeIneq.map_sum_le (q : QuadraticMap ℤ X ℝ) (hq : ∀ x, 0 ≤ q x) {I : Type} (s : Finset I)
    (v : I → X) : q (∑ x ∈ s, v x) ≤ s.card * ∑ x ∈ s, q (v x) := by sorry
