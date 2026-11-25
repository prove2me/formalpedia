-- Prove2me | Theorems.Thm_GlobalTheory_DiffDecay_Tame_decay
-- name    : GlobalTheory.DiffDecay.Tame.decay
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:04:09.576376+00:00
-- url     : https://prove2.me/theorems/b0bf14e1-3ada-4140-9baf-f61be4c088ae
-- title:
--   Tame: decay
-- statement:
--   The Tame construction uses the decay property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousSmulSemi.lean#L90-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousSmulSemi.lean#L90-L140

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousSmulSemi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap
open GlobalTheory.Published.Metaplectic
noncomputable section
open GlobalTheory GlobalTheory.DiffDecay
variable {E : Type} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] {W : Type} [SeminormedAddCommGroup W]

theorem GlobalTheory.DiffDecay.Tame.decay {R : W → E →ₗ[ℂ] E} (h : Tame R) (p : Seminorm ℂ E) (hp : Continuous p) (A C : ℝ) (N : ℕ) :
    ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ (s : W) (r : ℝ), 0 ≤ r → ‖s‖ ≤ A * r →
      (0 < r → ∃ u, ‖u‖ * r ≤ C ∧ ∀ f, p (R s (R u f + f)) = 0) → ∀ f, p (R s f) ≤ q f * (1 + r) ^ (-(N : ℝ)) := by sorry
