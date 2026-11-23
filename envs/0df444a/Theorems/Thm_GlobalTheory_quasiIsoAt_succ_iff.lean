-- Prove2me | Theorems.Thm_GlobalTheory_quasiIsoAt_succ_iff
-- name    : GlobalTheory.quasiIsoAt_succ_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:59.379863+00:00
-- url     : https://prove2.me/theorems/0a2cf4be-69a5-41d3-830e-77fce35b737c
-- title:
--   Global Theory: quasi Iso At succ iff
-- statement:
--   The Global Theory construction uses the quasi Iso At succ iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsFiniteProjectiveComplexQuasiIso.lean#L420-L428
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsFiniteProjectiveComplexQuasiIso.lean#L420-L428

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

theorem GlobalTheory.quasiIsoAt_succ_iff {K C : CochainComplex (ModuleCat.{v} R) ℕ} (φ : K ⟶ C) (p : ℕ) :
    QuasiIsoAt φ (p + 1) ↔
      (∀ y : C.X (p + 1), (C.d (p + 1) (p + 2)).hom y = 0 →
        ∃ (x : K.X (p + 1)) (z : C.X p), (K.d (p + 1) (p + 2)).hom x = 0 ∧
          (C.d p (p + 1)).hom z + (φ.f (p + 1)).hom x = y) ∧
      (∀ (x : K.X (p + 1)) (z : C.X p), (K.d (p + 1) (p + 2)).hom x = 0 →
        (C.d p (p + 1)).hom z = (φ.f (p + 1)).hom x → ∃ w : K.X p, (K.d p (p + 1)).hom w = x) := by sorry
