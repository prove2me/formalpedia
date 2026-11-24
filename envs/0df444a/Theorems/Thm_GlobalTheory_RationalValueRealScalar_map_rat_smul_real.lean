-- Prove2me | Theorems.Thm_GlobalTheory_RationalValueRealScalar_map_rat_smul_real
-- name    : GlobalTheory.RationalValueRealScalar.map_rat_smul_real
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:14:55.222986+00:00
-- url     : https://prove2.me/theorems/c69c6d62-91e0-49f1-bae9-884232a179c0
-- title:
--   Rational Value Real Scalar: map rat smul real
-- statement:
--   The Rational Value Real Scalar construction uses the map rat smul real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsRatBilinForm.lean#L5-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsRatBilinForm.lean#L5-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRatBilinForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.RationalValueRealScalar

theorem GlobalTheory.RationalValueRealScalar.map_rat_smul_real {U : Type} [AddCommGroup U] [Module ℝ U] {V : Type} [AddCommGroup V]
    [Module ℚ V] (p : V →+ U) (c : ℚ) (x : V) : p (c • x) = (c : ℝ) • p x := by sorry
