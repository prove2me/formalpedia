-- Prove2me | Theorems.Thm_GlobalTheory_UnitDiscAlg_norm_lt_one_of_pow_of_commute
-- name    : GlobalTheory.UnitDiscAlg.norm_lt_one_of_pow_of_commute
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:28:45.230889+00:00
-- url     : https://prove2.me/theorems/047e2a09-001e-4a5b-b156-485e93bc7ff9
-- title:
--   Unit Disc Alg: norm lt one of pow of commute
-- statement:
--   The Unit Disc Alg construction uses the norm lt one of pow of commute property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CommutingIntegralMatrixTopnil.lean#L39-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CommutingIntegralMatrixTopnil.lean#L39-L122

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UltrametricNormDetOneAddSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ClosedBallValuationSubringToSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommutingIntegralMatrixTopnil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open GlobalTheory GlobalTheory.UnitDiscAlg

theorem GlobalTheory.UnitDiscAlg.norm_lt_one_of_pow_of_commute (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E]
    (n : ℕ) (N : Matrix (Fin n) (Fin n) E) (hN : ∀ i j, ‖N i j‖ ≤ 1)
    (hb : ∃ u v : Polynomial E, (∀ i, ‖u.coeff i‖ ≤ 1) ∧ (∀ i, ‖v.coeff i‖ ≤ 1) ∧
      u * N.charpoly + v * Polynomial.derivative N.charpoly = 1)
    (w : Matrix (Fin n) (Fin n) E) (hwN : w * N = N * w) (hw : ∀ i j, ‖w i j‖ ≤ 1)
    (M : ℕ) (hM : ∀ i j, ‖(w ^ M) i j‖ < 1) : ∀ i j, ‖w i j‖ < 1 := by sorry
