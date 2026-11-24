-- Prove2me | Theorems.Thm_GlobalTheory_SummableSeriesBounds_decay
-- name    : GlobalTheory.SummableSeriesBounds.decay
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:23:36.882806+00:00
-- url     : https://prove2.me/theorems/0e82816d-7879-4e08-8079-455c66642ebd
-- title:
--   Summable Series Bounds: decay
-- statement:
--   The Summable Series Bounds construction uses the decay property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableNormMulPowOfBounded.lean#L172-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableNormMulPowOfBounded.lean#L172-L192

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableNormMulPowOfBounded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SummableSeriesBounds
open PowerSeries Filter Topology
variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]

theorem GlobalTheory.SummableSeriesBounds.decay {π : C} (hπ : ‖π‖ < 1) {b : ℝ} {G : PowerSeries C} (hb : ∀ m, ‖coeff m G‖ ≤ b)
    (n m : ℕ) : ‖coeff m ((X - PowerSeries.C π) ^ n * G)‖ ≤ ‖π‖ ^ (n - m) * b := by sorry
