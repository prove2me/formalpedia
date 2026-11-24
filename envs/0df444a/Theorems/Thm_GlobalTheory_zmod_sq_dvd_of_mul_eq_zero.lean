-- Prove2me | Theorems.Thm_GlobalTheory_zmod_sq_dvd_of_mul_eq_zero
-- name    : GlobalTheory.zmod_sq_dvd_of_mul_eq_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:25:25.315319+00:00
-- url     : https://prove2.me/theorems/1597ea2e-4140-4e52-83a3-011117be2912
-- title:
--   Global Theory: zmod sq dvd of mul eq zero
-- statement:
--   The Global Theory construction uses the zmod sq dvd of mul eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FlatModPSquaredTorsion.lean#L7-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FlatModPSquaredTorsion.lean#L7-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FlatModPSquaredTorsion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
open GlobalTheory

theorem GlobalTheory.zmod_sq_dvd_of_mul_eq_zero (p : ℕ) [hp : Fact p.Prime] (a : ZMod (p ^ 2))
    (ha : (p : ZMod (p ^ 2)) * a = 0) : ∃ c : ZMod (p ^ 2), a = (p : ZMod (p ^ 2)) * c := by sorry
