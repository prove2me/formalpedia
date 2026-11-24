-- Prove2me | Theorems.Thm_GlobalTheory_SummableSeriesBounds_bound_of_lin_mul
-- name    : GlobalTheory.SummableSeriesBounds.bound_of_lin_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:23:41.206058+00:00
-- url     : https://prove2.me/theorems/d0c470fe-2d18-4af5-94ae-98824aae0ed5
-- title:
--   Summable Series Bounds: bound of lin mul
-- statement:
--   The Summable Series Bounds construction uses the bound of lin mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableNormMulPowOfBounded.lean#L137-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableNormMulPowOfBounded.lean#L137-L158

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

theorem GlobalTheory.SummableSeriesBounds.bound_of_lin_mul {π : C} (hπ : ‖π‖ < 1) {G : PowerSeries C} {b c : ℝ}
    (hc : ∀ n, ‖coeff n G‖ ≤ c) (hb : ∀ n, ‖coeff n ((X - PowerSeries.C π) * G)‖ ≤ b) (m : ℕ) :
    ‖coeff m G‖ ≤ b := by sorry
