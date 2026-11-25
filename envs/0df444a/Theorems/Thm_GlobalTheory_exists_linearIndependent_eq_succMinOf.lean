-- Prove2me | Theorems.Thm_GlobalTheory_exists_linearIndependent_eq_succMinOf
-- name    : GlobalTheory.exists_linearIndependent_eq_succMinOf
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:34:12.68173+00:00
-- url     : https://prove2.me/theorems/d3d5f2a4-cb98-4b15-9771-031470e4a693
-- title:
--   Global Theory: exists linear Independent eq succ Min Of
-- statement:
--   The Global Theory construction uses the exists linear Independent eq succ Min Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsLinearIndependentSqrtEqSuccMinQuad.lean#L52-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsLinearIndependentSqrtEqSuccMinQuad.lean#L52-L81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsLinearIndependentSqrtEqSuccMinQuad
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule
open GlobalTheory
variable {K : Type*} [DivisionRing K] {V : Type*} [AddCommGroup V] [Module K V]
  {N : V → ℝ} {S : Set V} {n : ℕ}

theorem GlobalTheory.exists_linearIndependent_eq_succMinOf (hfin : ∀ R, {x | x ∈ S ∧ N x ≤ R}.Finite)
    (hN : ∀ x ∈ S, 0 ≤ N x) (hn : (n : Cardinal) ≤ Module.rank K (span K S)) :
    ∃ v : Fin n → V, LinearIndependent K v ∧ (∀ j, v j ∈ S) ∧
      ∀ j : Fin n, N (v j) = succMinOf K N S (j + 1) := by sorry
