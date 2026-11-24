-- Prove2me | Theorems.Thm_GlobalTheory_MaximalMinor_mem_span_of_det_update_mem
-- name    : GlobalTheory.MaximalMinor.mem_span_of_det_update_mem
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:21:06.076658+00:00
-- url     : https://prove2.me/theorems/427c8205-db57-49de-b528-bb35ad7528e6
-- title:
--   Maximal Minor: mem span of det update mem
-- statement:
--   The Maximal Minor construction uses the mem span of det update mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LinearIndependentOfDetMemNonZeroDivisors.lean#L34-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LinearIndependentOfDetMemNonZeroDivisors.lean#L34-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LinearIndependentOfDetMemNonZeroDivisors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule Function
open GlobalTheory
open GlobalTheory.MaximalMinor
variable {A R F ι κ : Type*} [CommRing A] [CommRing R] [Algebra A R] [AddCommGroup F]
  [Module R F] [Module A F] [IsScalarTower A R F] [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.MaximalMinor.mem_span_of_det_update_mem (b : Basis ι R F) {v : ι → F}
    (hv : b.det v ∈ nonZeroDivisors R) {x : F}
    (hx : ∀ i, b.det (update v i x) ∈ span A {b.det v}) : x ∈ span A (Set.range v) := by sorry
