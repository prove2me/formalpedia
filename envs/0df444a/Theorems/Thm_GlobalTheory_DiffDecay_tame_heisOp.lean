-- Prove2me | Theorems.Thm_GlobalTheory_DiffDecay_tame_heisOp
-- name    : GlobalTheory.DiffDecay.tame_heisOp
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:04:21.750443+00:00
-- url     : https://prove2.me/theorems/3190f13a-5f1a-4a61-a18c-74cb4ed43534
-- title:
--   Diff Decay: tame heis Op
-- statement:
--   The Diff Decay construction uses the tame heis Op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousSmulSemi.lean#L151-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousSmulSemi.lean#L151-L188

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
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {W : Type} [SeminormedAddCommGroup W]

theorem GlobalTheory.DiffDecay.tame_heisOp
    (hT : ∀ p : Seminorm ℂ (SchwartzMap V ℂ), Continuous p →
      ∃ (q : Seminorm ℂ (SchwartzMap V ℂ)) (M : ℕ), Continuous q ∧ ∀ (a : V) (f : SchwartzMap V ℂ),
        p (SchwartzMap.compSubConstCLM ℂ (-a) f - f) ≤ ‖a‖ * (1 + ‖a‖) ^ M * q f)
    (hP : ∀ p : Seminorm ℂ (SchwartzMap V ℂ), Continuous p →
      ∃ (q : Seminorm ℂ (SchwartzMap V ℂ)) (M : ℕ), Continuous q ∧ ∀ (L : V →L[ℝ] ℝ) (k : ℝ) (f : SchwartzMap V ℂ),
        p (SchwartzMap.smulLeftCLM ℂ (fun y => eChar (L y + k)) f - f) ≤ (‖L‖ + |k|) * (1 + ‖L‖) ^ M * q f)
    (L : W → V →L[ℝ] ℝ) (k : W → ℝ) (a : W → V) (c : ℝ) (hc : 1 ≤ c) (hL : ∀ w, ‖L w‖ ≤ c * ‖w‖)
    (hk : ∀ w, |k w| ≤ c * ‖w‖ ^ 2) (ha : ∀ w, ‖a w‖ ≤ ‖w‖) :
    Tame fun w => (heisOp (L w) (k w) (a w)).toLinearMap := by sorry
