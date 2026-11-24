-- Prove2me | Theorems.Thm_GlobalTheory_exists_norm_pow_eq_of_isAlgClosed
-- name    : GlobalTheory.exists_norm_pow_eq_of_isAlgClosed
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:36:04.740563+00:00
-- url     : https://prove2.me/theorems/c91084d5-3d7a-42b5-a00b-c91581760b17
-- title:
--   Global Theory: exists norm pow eq of is Alg Closed
-- statement:
--   The Global Theory construction uses the exists norm pow eq of is Alg Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAbsoluteValueOfIsDiscreteValuationRing.lean#L215-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAbsoluteValueOfIsDiscreteValuationRing.lean#L215-L218

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowLeComapMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
universe u

theorem GlobalTheory.exists_norm_pow_eq_of_isAlgClosed {C : Type*} [NormedField C] [IsAlgClosed C] (x : C)
    {n : ℕ} (hn : 0 < n) : ∃ y : C, ‖y‖ ^ n = ‖x‖ := by sorry
