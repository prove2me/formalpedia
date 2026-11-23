-- Prove2me | Theorems.Thm_GlobalTheory_CharFormDeriv_seminorm_rem_mul_le
-- name    : GlobalTheory.CharFormDeriv.seminorm_rem_mul_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:21:22.831325+00:00
-- url     : https://prove2.me/theorems/446ff91a-6ad9-41b6-879a-18b7d5a52904
-- title:
--   Char Form Deriv: seminorm rem mul le
-- statement:
--   The Char Form Deriv construction uses the seminorm rem mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivRemCompLe.lean#L176-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivRemCompLe.lean#L176-L235

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

theorem GlobalTheory.CharFormDeriv.seminorm_rem_mul_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℝ) (f u : SchwartzMap V ℂ) {t : ℝ} (ht0 : t ≠ 0) (ht1 : |t| ≤ 1)
    (hu : ∀ x, u x = rem t (L x) * f x) (k n : ℕ) :
    SchwartzMap.seminorm ℂ k n u ≤ |t| * (3 * 2 ^ n * (1 + ‖L‖) ^ (n + 2) *
      (2 ^ (k + 2) * ((Finset.Iic (k + 2, n)).sup fun m => SchwartzMap.seminorm ℂ m.1 m.2) f)) := by sorry
