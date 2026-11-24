-- Prove2me | Theorems.Thm_GlobalTheory_coeff_mul_X_ite
-- name    : GlobalTheory.coeff_mul_X_ite
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:09:59.434339+00:00
-- url     : https://prove2.me/theorems/01a1e43e-7fc2-46c3-9646-e94bb167e68d
-- title:
--   Global Theory: coeff mul X ite
-- statement:
--   The Global Theory construction uses the coeff mul X ite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MvPowerSeriesVariablesSyzygySocle.lean#L7-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MvPowerSeriesVariablesSyzygySocle.lean#L7-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MvPowerSeriesVariablesSyzygySocle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
open MvPowerSeries Finsupp

theorem GlobalTheory.coeff_mul_X_ite {k : Type} [CommRing k] {g : ℕ} (f : MvPowerSeries (Fin g) k)
    (j : Fin g) (m : Fin g →₀ ℕ) :
    coeff m (f * X j) = if m j ≠ 0 then coeff (m - single j 1) f else 0 := by sorry
