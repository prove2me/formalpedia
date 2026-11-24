-- Prove2me | Theorems.Thm_GlobalTheory_CharFormDeriv_norm_iteratedFDeriv_rem_comp_le
-- name    : GlobalTheory.CharFormDeriv.norm_iteratedFDeriv_rem_comp_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:07:32.178607+00:00
-- url     : https://prove2.me/theorems/b7a9e0e9-68ac-4348-a1a8-14f2d8076503
-- title:
--   Char Form Deriv: norm iterated FDeriv rem comp le
-- statement:
--   The Char Form Deriv construction uses the norm iterated FDeriv rem comp le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivRemCompLe.lean#L135-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivRemCompLe.lean#L135-L148

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivRemCompLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open GlobalTheory GlobalTheory.CharFormDeriv

theorem GlobalTheory.CharFormDeriv.norm_iteratedFDeriv_rem_comp_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℝ) {t : ℝ} (ht0 : t ≠ 0) (ht1 : |t| ≤ 1) (i : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ i (fun x => rem t (L x)) x‖ ≤ 3 * |t| * (1 + ‖L‖ * ‖x‖) ^ 2 * ‖L‖ ^ i := by sorry
