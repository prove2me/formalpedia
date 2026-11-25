-- Prove2me | Theorems.Thm_GlobalTheory_exists_basis_span_eq_of_discrete
-- name    : GlobalTheory.exists_basis_span_eq_of_discrete
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:02:05.608077+00:00
-- url     : https://prove2.me/theorems/a515fed7-d59d-4fc2-b5fd-5a4382c5a828
-- title:
--   Global Theory: exists basis span eq of discrete
-- statement:
--   The Global Theory construction uses the exists basis span eq of discrete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/ExistsBasisSpanEqOfDiscrete.lean#L8-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/ExistsBasisSpanEqOfDiscrete.lean#L8-L20

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Transference
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_ExistsBasisSpanEqOfDiscrete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
open GlobalTheory

theorem GlobalTheory.exists_basis_span_eq_of_discrete {N : ℕ} (M : Submodule ℤ (EuclideanSpace ℝ (Fin N)))
    [DiscreteTopology M] (hM : span ℝ (M : Set (EuclideanSpace ℝ (Fin N))) = ⊤) :
    ∃ b : Basis (Fin N) ℝ (EuclideanSpace ℝ (Fin N)), span ℤ (Set.range b) = M := by sorry
