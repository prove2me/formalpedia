-- Prove2me | Theorems.Thm_GlobalTheory_UnitDiscAlg_Red_sm_mul_left
-- name    : GlobalTheory.UnitDiscAlg.Red.sm_mul_left
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:27:07.697265+00:00
-- url     : https://prove2.me/theorems/ea27aba6-86b2-4fe6-89da-956f1490dc17
-- title:
--   Red: sm mul left
-- statement:
--   The Red construction uses the sm mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CommutingIntegralMatrixDecompose.lean#L30-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CommutingIntegralMatrixDecompose.lean#L30-L36

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

theorem GlobalTheory.UnitDiscAlg.Red.sm_mul_left {x y : Matrix (Fin n) (Fin n) E} (hx : ∀ i j, ‖x i j‖ ≤ 1) (hy : Sm y) :
    Sm (x * y) := by sorry
