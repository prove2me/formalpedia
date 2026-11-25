-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_LineStabiliser_acts_through_level_one
-- name    : GlobalTheory.HCXi.LineStabiliser.acts_through_level_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:19:11.845263+00:00
-- url     : https://prove2.me/theorems/4ae2e870-eb6b-4a3e-917d-3bddb988a3ce
-- title:
--   Line Stabiliser: acts through level one
-- statement:
--   The Line Stabiliser construction uses the acts through level one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ParabolicLineStabilizerLevi.lean#L89-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ParabolicLineStabilizerLevi.lean#L89-L116

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LevMulVecOutside
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ParabolicLineStabilizerLevi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.LineStabiliser
open GlobalTheory.LevelUnitary GlobalTheory.LevelStabiliser
variable (k r' : ℕ)

theorem GlobalTheory.HCXi.LineStabiliser.acts_through_level_one : ∀ (k r' : ℕ) (a : ℂ), ∀ p ∈ GV k (1 + r'), p *ᵥ e0 k r' = a • e0 k r' → a ≠ 0 ∧ ∃ g₁ ∈ GV k r', ∀ w : Fin (2 * r' + k + 1) → ℂ, ∃ c : ℂ, p *ᵥ liftVec k 1 r' w = liftVec k 1 r' (g₁ *ᵥ w) + c • e0 k r' := by sorry
