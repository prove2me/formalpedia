-- Prove2me | Theorems.Thm_GlobalTheory_killed_span_adjoin_finrank_le
-- name    : GlobalTheory.killed_span_adjoin_finrank_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:02:29.85283+00:00
-- url     : https://prove2.me/theorems/57ebb98a-5e65-432f-ad99-c7d2dc76fd75
-- title:
--   Global Theory: killed span adjoin finrank le
-- statement:
--   The Global Theory construction uses the killed span adjoin finrank le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteDimensionalSpanAlgebraOrbitOfAnnihilated.lean#L165-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteDimensionalSpanAlgebraOrbitOfAnnihilated.lean#L165-L229

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteDimensionalSpanAlgebraOrbitOfAnnihilated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

open Polynomial

theorem GlobalTheory.killed_span_adjoin_finrank_le :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (T : Finset (Module.End ℂ V))
      (p : Module.End ℂ V → Polynomial ℂ), (∀ s ∈ T, ∀ t ∈ T, Commute s t) →
      (∀ t ∈ T, p t ≠ 0) → ∀ ψ : V, (∀ t ∈ T, Polynomial.aeval t (p t) ψ = 0) →
      FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) ''
        (Algebra.adjoin ℂ (T : Set (Module.End ℂ V)) : Set (Module.End ℂ V)))) ∧
      Module.finrank ℂ (Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) ''
        (Algebra.adjoin ℂ (T : Set (Module.End ℂ V)) : Set (Module.End ℂ V)))) ≤
        ∏ t ∈ T, (p t).natDegree := by sorry
