-- Prove2me | Theorems.Thm_GlobalTheory_UnitDiscAlg_Red_sm_eq_smul
-- name    : GlobalTheory.UnitDiscAlg.Red.sm_eq_smul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:27:00.905249+00:00
-- url     : https://prove2.me/theorems/a0485cec-10b2-4dab-b534-435d9c074692
-- title:
--   Red: sm eq smul
-- statement:
--   The Red construction uses the sm eq smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CommutingIntegralMatrixDecompose.lean#L46-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CommutingIntegralMatrixDecompose.lean#L46-L55

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

theorem GlobalTheory.UnitDiscAlg.Red.sm_eq_smul {N s : Matrix (Fin n) (Fin n) E} {ϖ : E} (h0 : 0 < ‖ϖ‖)
    (hu : ∀ y : E, ‖y‖ < 1 → ‖y‖ ≤ ‖ϖ‖) (hs : Sm s) (hc : s * N = N * s) :
    ∃ a : Matrix (Fin n) (Fin n) E, a * N = N * a ∧ (∀ i j, ‖a i j‖ ≤ 1) ∧ s = ϖ • a := by sorry
