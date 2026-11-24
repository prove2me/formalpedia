-- Prove2me | Theorems.Thm_GlobalTheory_exists_fin_independent_span_eq
-- name    : GlobalTheory.exists_fin_independent_span_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:31:23.608797+00:00
-- url     : https://prove2.me/theorems/bbc989f0-a0b3-46f3-b7de-e15c60cccf20
-- title:
--   Global Theory: exists fin independent span eq
-- statement:
--   The Global Theory construction uses the exists fin independent span eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsBasisAdaptedTwoSubspaces.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsBasisAdaptedTwoSubspaces.lean#L11-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsBasisAdaptedTwoSubspaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.exists_fin_independent_span_eq {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : Submodule K V) :
    ∃ (n : ℕ) (v : Fin n → V), LinearIndependent K v ∧ Submodule.span K (Set.range v) = S := by sorry
