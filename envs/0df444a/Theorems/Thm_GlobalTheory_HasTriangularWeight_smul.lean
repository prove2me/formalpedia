-- Prove2me | Theorems.Thm_GlobalTheory_HasTriangularWeight_smul
-- name    : GlobalTheory.HasTriangularWeight.smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:43:27.432859+00:00
-- url     : https://prove2.me/theorems/f4e0099c-457d-4461-ad35-a0e920301dcf
-- title:
--   Has Triangular Weight: smul
-- statement:
--   The Has Triangular Weight construction uses the smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsUnitEvalOfMapResidueNeZero.lean#L133-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsUnitEvalOfMapResidueNeZero.lean#L133-L139

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Module
open GlobalTheory
variable {ι : Type*} {K : Type*} {V : ι → Type*}
variable [Fintype ι] {r : ι → ℕ} [Field K] [∀ s, AddCommGroup (V s)] [∀ s, Module K (V s)]
  {W : Type*} [AddCommGroup W] [Module K W]

theorem GlobalTheory.HasTriangularWeight.smul {a : ∀ s, Fin (r s) → ℕ} {P : (∀ s, Fin (r s) → V s) → W}
    (hP : HasTriangularWeight K a P) (x : ∀ s, Fin (r s) → V s) (d : ∀ s, Fin (r s) → K)
    (hd : ∀ s i, d s i ≠ 0) :
    P (fun s i => d s i • x s i) = (∏ s, ∏ i, d s i ^ a s i) • P x := by sorry
