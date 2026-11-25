-- Prove2me | Theorems.Thm_GlobalTheory_MaximalMinor_exists_det_ne_zero
-- name    : GlobalTheory.MaximalMinor.exists_det_ne_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:14:09.891835+00:00
-- url     : https://prove2.me/theorems/d29b5921-452b-484c-85d5-c57331c7da58
-- title:
--   Maximal Minor: exists det ne zero
-- statement:
--   The Maximal Minor construction uses the exists det ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LinearIndependentOfDetMemNonZeroDivisors.lean#L59-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LinearIndependentOfDetMemNonZeroDivisors.lean#L59-L70

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

theorem GlobalTheory.MaximalMinor.exists_det_ne_zero [IsDomain R] (b : Basis ι R F) (G : κ → F)
    (hr : Fintype.card ι ≤ finrank R (span R (Set.range G))) :
    ∃ σ : ι → κ, b.det (G ∘ σ) ≠ 0 := by sorry
