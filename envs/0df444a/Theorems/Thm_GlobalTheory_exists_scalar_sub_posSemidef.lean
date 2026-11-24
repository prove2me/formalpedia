-- Prove2me | Theorems.Thm_GlobalTheory_exists_scalar_sub_posSemidef
-- name    : GlobalTheory.exists_scalar_sub_posSemidef
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:40:46.792861+00:00
-- url     : https://prove2.me/theorems/42fe4985-f906-4585-bb4e-9f68e569fe34
-- title:
--   Global Theory: exists scalar sub pos Semidef
-- statement:
--   The Global Theory construction uses the exists scalar sub pos Semidef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsScalarSubPosSemidef.lean#L9-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsScalarSubPosSemidef.lean#L9-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsScalarSubPosSemidef
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
open GlobalTheory
open scoped MatrixOrder Matrix.Norms.L2Operator

theorem GlobalTheory.exists_scalar_sub_posSemidef {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (hA : A.IsHermitian) :
    ∃ c : ℝ, 1 ≤ c ∧ ((c : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) - A).PosSemidef := by sorry
