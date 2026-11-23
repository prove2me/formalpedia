-- Prove2me | Theorems.Thm_GlobalTheory_cochain_comm_apply
-- name    : GlobalTheory.cochain_comm_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:03.195749+00:00
-- url     : https://prove2.me/theorems/23371056-3dac-455d-82f4-f393966f534f
-- title:
--   Global Theory: cochain comm apply
-- statement:
--   The Global Theory construction uses the cochain comm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsFiniteProjectiveComplexQuasiIso.lean#L399-L401
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsFiniteProjectiveComplexQuasiIso.lean#L399-L401

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory TensorProduct
universe u v w
open GlobalTheory
variable {R : Type u} [Ring R]

theorem GlobalTheory.cochain_comm_apply {K C : CochainComplex (ModuleCat.{v} R) ℕ} (φ : K ⟶ C) (i j : ℕ)
    (x : K.X i) : (C.d i j).hom ((φ.f i).hom x) = (φ.f j).hom ((K.d i j).hom x) := by sorry
