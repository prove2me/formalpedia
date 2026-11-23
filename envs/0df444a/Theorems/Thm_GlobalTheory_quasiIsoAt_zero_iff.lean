-- Prove2me | Theorems.Thm_GlobalTheory_quasiIsoAt_zero_iff
-- name    : GlobalTheory.quasiIsoAt_zero_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:58.709856+00:00
-- url     : https://prove2.me/theorems/358a02d4-2df9-4d06-8f3a-595fd916c6f7
-- title:
--   Global Theory: quasi Iso At zero iff
-- statement:
--   The Global Theory construction uses the quasi Iso At zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsFiniteProjectiveComplexQuasiIso.lean#L403-L418
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsFiniteProjectiveComplexQuasiIso.lean#L403-L418

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

theorem GlobalTheory.quasiIsoAt_zero_iff {K C : CochainComplex (ModuleCat.{v} R) ℕ} (φ : K ⟶ C) :
    QuasiIsoAt φ 0 ↔
      (∀ y : C.X 0, (C.d 0 1).hom y = 0 → ∃ x : K.X 0, (K.d 0 1).hom x = 0 ∧ (φ.f 0).hom x = y) ∧
      (∀ x : K.X 0, (K.d 0 1).hom x = 0 → (φ.f 0).hom x = 0 → x = 0) := by sorry
