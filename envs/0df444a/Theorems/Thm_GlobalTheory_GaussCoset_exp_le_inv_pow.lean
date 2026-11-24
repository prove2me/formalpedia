-- Prove2me | Theorems.Thm_GlobalTheory_GaussCoset_exp_le_inv_pow
-- name    : GlobalTheory.GaussCoset.exp_le_inv_pow
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:48:51.254798+00:00
-- url     : https://prove2.me/theorems/08400a89-ae4e-4b8b-a2b1-08e1e87e2593
-- title:
--   Gauss Coset: exp le inv pow
-- statement:
--   The Gauss Coset construction uses the exp le inv pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/SummableGaussianCoset.lean#L7-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/SummableGaussianCoset.lean#L7-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SummableGaussianCoset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open GlobalTheory GlobalTheory.GaussCoset

theorem GlobalTheory.GaussCoset.exp_le_inv_pow {c : ℝ} (hc : 0 < c) (R : ℝ) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Real.exp (-c * t ^ 2 + R * t) ≤
      ((n.factorial : ℝ) * Real.exp ((R + 1) ^ 2 / (4 * c))) * t⁻¹ ^ n := by sorry
