-- Prove2me | Theorems.Thm_GlobalTheory_DiffDecay_Tame_growth
-- name    : GlobalTheory.DiffDecay.Tame.growth
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:17:45.637248+00:00
-- url     : https://prove2.me/theorems/64527d33-99e7-49b6-97c6-f3490cb39e09
-- title:
--   Tame: growth
-- statement:
--   The Tame construction uses the growth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousSmulSemi.lean#L57-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousSmulSemi.lean#L57-L70

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

theorem GlobalTheory.DiffDecay.Tame.growth {R : W → E →ₗ[ℂ] E} (h : Tame R) (p : Seminorm ℂ E) (hp : Continuous p) :
    ∃ (q : Seminorm ℂ E) (M : ℕ), Continuous q ∧ ∀ w f, p (R w f) ≤ (1 + ‖w‖) ^ M * q f := by sorry
