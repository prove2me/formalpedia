-- Prove2me | Theorems.Thm_GlobalTheory_UnitDiscAlg_Red_exists_pow_close
-- name    : GlobalTheory.UnitDiscAlg.Red.exists_pow_close
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:26:48.482916+00:00
-- url     : https://prove2.me/theorems/ed8a5ae3-a8ca-47e3-94d3-722c70841fa7
-- title:
--   Red: exists pow close
-- statement:
--   The Red construction uses the exists pow close property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CommutingIntegralMatrixDecompose.lean#L62-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CommutingIntegralMatrixDecompose.lean#L62-L82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommOfBezout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommutingIntegralMatrixTopnilStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommutingIntegralMatrixDecompose
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitDiscAlg
open GlobalTheory GlobalTheory.UnitDiscAlg GlobalTheory.UnitDiscAlg.Red
variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ}

theorem GlobalTheory.UnitDiscAlg.Red.exists_pow_close [LocallyCompactSpace E] (y : Matrix (Fin n) (Fin n) E)
    (hy : ∀ i j, ‖y i j‖ ≤ 1) : ∃ a b : ℕ, a < b ∧ Sm (y ^ b - y ^ a) := by sorry
