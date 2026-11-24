-- Prove2me | Theorems.Thm_GlobalTheory_DecayOfMemSpan_decay_of_mem_span
-- name    : GlobalTheory.DecayOfMemSpan.decay_of_mem_span
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:35:28.606159+00:00
-- url     : https://prove2.me/theorems/d49c2712-c879-4199-b7d6-3c40cc4af0f8
-- title:
--   Decay Of Mem Span: decay of mem span
-- statement:
--   The Decay Of Mem Span construction uses the decay of mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DecayOfMemSpan.lean#L5-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DecayOfMemSpan.lean#L5-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DecayOfMemSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DecayOfMemSpan

theorem GlobalTheory.DecayOfMemSpan.decay_of_mem_span {G H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ρ : G → H →L[ℂ] H} {D : G → ℝ} {c : ℝ} {S : Set H} {u : H}
    (h : ∀ v ∈ S, ∃ C : ℝ, ∀ g : G,
      ‖Inner.inner ℂ v ((ρ g : H → H) u)‖ ≤ C * Real.exp (-(c * D g))) :
    ∀ v ∈ Submodule.span ℂ S, ∃ C : ℝ, ∀ g : G,
      ‖Inner.inner ℂ v ((ρ g : H → H) u)‖ ≤ C * Real.exp (-(c * D g)) := by sorry
