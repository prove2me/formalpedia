-- Prove2me | Theorems.Thm_GlobalTheory_SummableSeriesBounds_bound_of_lin_pow_mul
-- name    : GlobalTheory.SummableSeriesBounds.bound_of_lin_pow_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:23:47.115365+00:00
-- url     : https://prove2.me/theorems/98cb168a-46f9-435a-b68f-1247ffe21f86
-- title:
--   Summable Series Bounds: bound of lin pow mul
-- statement:
--   The Summable Series Bounds construction uses the bound of lin pow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableNormMulPowOfBounded.lean#L160-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableNormMulPowOfBounded.lean#L160-L170

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

theorem GlobalTheory.SummableSeriesBounds.bound_of_lin_pow_mul {π : C} (hπ : ‖π‖ < 1) {b : ℝ} (n : ℕ) (G : bdd C)
    (hb : ∀ m, ‖coeff m ((lin π ^ n * G : bdd C) : PowerSeries C)‖ ≤ b) (m : ℕ) :
    ‖coeff m (G : PowerSeries C)‖ ≤ b := by sorry
