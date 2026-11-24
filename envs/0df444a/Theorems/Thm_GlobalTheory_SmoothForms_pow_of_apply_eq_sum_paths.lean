-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_pow_of_apply_eq_sum_paths
-- name    : GlobalTheory.SmoothForms.pow_of_apply_eq_sum_paths
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:19:16.131376+00:00
-- url     : https://prove2.me/theorems/b112dc85-4d00-4652-9e0d-fd20728206a3
-- title:
--   Smooth Forms: pow of apply eq sum paths
-- statement:
--   The Smooth Forms construction uses the pow of apply eq sum paths property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/CommuteGelfandInvariantMatrixUnitsOfGlRel.lean#L18-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/CommuteGelfandInvariantMatrixUnitsOfGlRel.lean#L18-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PowEntryCommutator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommuteGelfandInvariantMatrixUnitsOfGlRel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
open GlobalTheory GlobalTheory.SmoothForms
variable {A : Type} [Ring A] {n : ℕ}

theorem GlobalTheory.SmoothForms.pow_of_apply_eq_sum_paths (E : Fin n → Fin n → A) (k : ℕ) (c e : Fin n) :
    (Matrix.of E ^ (k + 1)) c e = ∑ idx : Fin k → Fin n, (List.ofFn fun a : Fin (k + 1) =>
      E ((Fin.cons c idx : Fin (k + 1) → Fin n) a) ((Fin.snoc idx e : Fin (k + 1) → Fin n) a)).prod := by sorry
