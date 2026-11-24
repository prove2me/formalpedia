-- Prove2me | Theorems.Thm_GlobalTheory_DiffDecay_Tame_iter
-- name    : GlobalTheory.DiffDecay.Tame.iter
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:49:34.22687+00:00
-- url     : https://prove2.me/theorems/617d9f3a-1f03-4174-ae5d-62c9f32cca26
-- title:
--   Tame: iter
-- statement:
--   The Tame construction uses the iter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousSmulSemi.lean#L72-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousSmulSemi.lean#L72-L88

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

theorem GlobalTheory.DiffDecay.Tame.iter {R : W → E →ₗ[ℂ] E} (h : Tame R) (j : ℕ) (p : Seminorm ℂ E) (hp : Continuous p) :
    ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ u, ‖u‖ ≤ 1 → ∀ f, p (((R u - 1) ^ j) f) ≤ ‖u‖ ^ j * q f := by sorry
