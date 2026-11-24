-- Prove2me | Theorems.Thm_GlobalTheory_MaximalMinor_det_ne_zero_of_linearIndependent
-- name    : GlobalTheory.MaximalMinor.det_ne_zero_of_linearIndependent
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:21:05.996107+00:00
-- url     : https://prove2.me/theorems/40bc9397-2ffe-4499-b695-ab7354ae57bb
-- title:
--   Maximal Minor: det ne zero of linear Independent
-- statement:
--   The Maximal Minor construction uses the det ne zero of linear Independent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LinearIndependentOfDetMemNonZeroDivisors.lean#L24-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LinearIndependentOfDetMemNonZeroDivisors.lean#L24-L32

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

theorem GlobalTheory.MaximalMinor.det_ne_zero_of_linearIndependent [IsDomain R] (b : Basis ι R F) {v : ι → F}
    (hv : LinearIndependent R v) : b.det v ≠ 0 := by sorry
