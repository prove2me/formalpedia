-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_sum_fin_succ_fun_cons
-- name    : GlobalTheory.SmoothForms.sum_fin_succ_fun_cons
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:51.178155+00:00
-- url     : https://prove2.me/theorems/829869d2-866e-4668-8b54-c854e4069455
-- title:
--   Smooth Forms: sum fin succ fun cons
-- statement:
--   The Smooth Forms construction uses the sum fin succ fun cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/CommuteGelfandInvariantMatrixUnitsOfGlRel.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/CommuteGelfandInvariantMatrixUnitsOfGlRel.lean#L13-L16

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

theorem GlobalTheory.SmoothForms.sum_fin_succ_fun_cons {M : Type} [AddCommMonoid M] (k : ℕ) (f : (Fin (k + 1) → Fin n) → M) :
    ∑ idx, f idx = ∑ c : Fin n, ∑ idx : Fin k → Fin n, f (Fin.cons c idx) := by sorry
