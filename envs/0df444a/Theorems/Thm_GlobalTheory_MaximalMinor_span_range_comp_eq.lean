-- Prove2me | Theorems.Thm_GlobalTheory_MaximalMinor_span_range_comp_eq
-- name    : GlobalTheory.MaximalMinor.span_range_comp_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:13:56.432566+00:00
-- url     : https://prove2.me/theorems/4cd842be-a26f-4248-bcd3-41b628c82e47
-- title:
--   Maximal Minor: span range comp eq
-- statement:
--   The Maximal Minor construction uses the span range comp eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LinearIndependentOfDetMemNonZeroDivisors.lean#L49-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LinearIndependentOfDetMemNonZeroDivisors.lean#L49-L57

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

theorem GlobalTheory.MaximalMinor.span_range_comp_eq (b : Basis ι R F) (G : κ → F) {σ : ι → κ}
    (hσ : b.det (G ∘ σ) ∈ nonZeroDivisors R)
    (h : ∀ τ : ι → κ, b.det (G ∘ τ) ∈ span A {b.det (G ∘ σ)}) :
    span A (Set.range (G ∘ σ)) = span A (Set.range G) := by sorry
