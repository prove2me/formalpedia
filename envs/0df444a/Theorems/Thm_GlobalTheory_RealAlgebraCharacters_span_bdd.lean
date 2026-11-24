-- Prove2me | Theorems.Thm_GlobalTheory_RealAlgebraCharacters_span_bdd
-- name    : GlobalTheory.RealAlgebraCharacters.span_bdd
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:15:24.104256+00:00
-- url     : https://prove2.me/theorems/9a2eeb14-1bbc-4fc8-8ce6-82e0e79f5e40
-- title:
--   Real Algebra Characters: span bdd
-- statement:
--   The Real Algebra Characters construction uses the span bdd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RealAlgSep.lean#L37-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RealAlgSep.lean#L37-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RealAlgSep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.RealAlgebraCharacters
open Filter Topology
variable {X : Type} {B : Type} [AddCommGroup B] (χ : B → X → ℂ)
omit [AddCommGroup B]

theorem GlobalTheory.RealAlgebraCharacters.span_bdd (hn : ∀ (a : B) (x : X), ‖χ a x‖ = 1)
    {f : X → ℂ} (hf : f ∈ Submodule.span ℂ (Set.range χ)) : ∃ M : ℝ, ∀ x, ‖f x‖ ≤ M := by sorry
