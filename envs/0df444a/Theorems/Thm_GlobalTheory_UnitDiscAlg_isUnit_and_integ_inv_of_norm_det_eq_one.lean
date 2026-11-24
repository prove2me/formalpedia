-- Prove2me | Theorems.Thm_GlobalTheory_UnitDiscAlg_isUnit_and_integ_inv_of_norm_det_eq_one
-- name    : GlobalTheory.UnitDiscAlg.isUnit_and_integ_inv_of_norm_det_eq_one
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:26:54.588732+00:00
-- url     : https://prove2.me/theorems/dd70ba9c-31bc-41c2-be59-058f1294bd0b
-- title:
--   Unit Disc Alg: is Unit and integ inv of norm det eq one
-- statement:
--   The Unit Disc Alg construction uses the is Unit and integ inv of norm det eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsUnitAndIntegInvOfNormDetEqOne.lean#L17-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsUnitAndIntegInvOfNormDetEqOne.lean#L17-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommOfBezout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsUnitAndIntegInvOfNormDetEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitDiscAlg
open GlobalTheory GlobalTheory.UnitDiscAlg

theorem GlobalTheory.UnitDiscAlg.isUnit_and_integ_inv_of_norm_det_eq_one :
    ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] (n : ℕ)
      (x : Matrix (Fin n) (Fin n) E), (∀ i j, ‖x i j‖ ≤ 1) → ‖x.det‖ = 1 →
      IsUnit x ∧ ∀ i j, ‖x⁻¹ i j‖ ≤ 1 := by sorry
